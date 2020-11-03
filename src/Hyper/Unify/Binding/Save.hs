-- | Serialize the state of unification

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Unify.Binding.Save
    ( save
    ) where

import qualified Control.Lens as Lens
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..))
import qualified Data.Sequence as Sequence
import           Hyper
import           Hyper.Class.Optic (HLens, hLens)
import           Hyper.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           Hyper.Recurse
import           Hyper.Unify.Binding (Binding, _Binding, UVar(..))
import           Hyper.Unify.Term (UTerm(..), uBody)

import           Hyper.Internal.Prelude

saveUTerm ::
    forall m typeVars t.
    (Unify m t, Recursively (HLens typeVars) t) =>
    UTerm (UVarOf m) # t ->
    StateT (typeVars # Binding, [m ()]) m (UTerm UVar # t)
saveUTerm (UUnbound c) = UUnbound c & pure
saveUTerm (USkolem c) = USkolem c & pure
saveUTerm (UToVar v) = saveVar v <&> UToVar
saveUTerm (UTerm u) = uBody saveBody u <&> UTerm
saveUTerm UInstantiated{} = error "converting bindings during instantiation"
saveUTerm UResolving{} = error "converting bindings after resolution"
saveUTerm UResolved{} = error "converting bindings after resolution"
saveUTerm UConverted{} = error "converting variable again"

saveVar ::
    forall m t typeVars.
    (Unify m t, Recursively (HLens typeVars) t) =>
    UVarOf m # t ->
    StateT (typeVars # Binding, [m ()]) m (UVar # t)
saveVar v =
    withDict (recursively (Proxy @(HLens typeVars t))) $
    lookupVar binding v & lift
    >>=
    \case
    UConverted i -> pure (UVar i)
    srcBody ->
        do
            pb <- Lens.use (Lens._1 . hLens)
            let r = pb ^. _Binding & Sequence.length
            UConverted r & bindVar binding v & lift
            Lens._2 %= (<> [bindVar binding v srcBody])
            dstBody <- saveUTerm srcBody
            Lens._1 . hLens .= (pb & _Binding %~ (Sequence.|> dstBody))
            UVar r & pure

saveBody ::
    forall m typeVars t.
    (Unify m t, Recursively (HLens typeVars) t) =>
    t # UVarOf m ->
    StateT (typeVars # Binding, [m ()]) m (t # UVar)
saveBody =
    withDict (recurse (Proxy @(Unify m t))) $
    withDict (recursively (Proxy @(HLens typeVars t))) $
    htraverse
    ( Proxy @(Unify m) #*# Proxy @(Recursively (HLens typeVars))
        #> saveVar
    )

-- | Serialize the state of unification for
-- the unification variables in a given value,
-- and transform the value's unification variables
-- to their serialized identifiers.
save ::
    (Unify m t, Recursively (HLens typeVars) t) =>
    t # UVarOf m ->
    StateT (typeVars # Binding) m (t # UVar)
save collection =
    StateT $
    \dstState ->
    do
        (r, (finalState, recover)) <- runStateT (saveBody collection) (dstState, [])
        (r, finalState) <$ sequence_ recover
