{-# LANGUAGE FlexibleContexts #-}

-- | Serialize the state of unification
module Hyper.Unify.Binding.Save
    ( save
    ) where

import qualified Control.Lens as Lens
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Trans.State (StateT (..))
import Hyper
import Hyper.Class.Optic (HNodeLens (..))
import Hyper.Class.Unify (BindingDict (..), UVarOf, Unify (..))
import Hyper.Recurse
import Hyper.Unify.Binding (Binding, UVar (..), _Binding)
import Hyper.Unify.Term (UTerm (..), uBody)

import Hyper.Internal.Prelude

saveUTerm ::
    forall m typeVars t.
    (Unify m t, Recursively (HNodeLens typeVars) t) =>
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
    (Unify m t, Recursively (HNodeLens typeVars) t) =>
    UVarOf m # t ->
    StateT (typeVars # Binding, [m ()]) m (UVar # t)
saveVar v =
    lookupVar binding v
        & lift
        >>= \case
            UConverted i -> pure (UVar i)
            srcBody ->
                do
                    pb <- Lens.use (Lens._1 . hNodeLens)
                    let r = pb ^. _Binding & length
                    UConverted r & bindVar binding v & lift
                    Lens._2 %= (<> [bindVar binding v srcBody])
                    dstBody <- saveUTerm srcBody
                    Lens._1 . hNodeLens .= (pb & _Binding %~ (Lens.|> dstBody))
                    UVar r & pure
                    \\ recursively (Proxy @(HNodeLens typeVars t))

saveBody ::
    forall m typeVars t.
    (Unify m t, Recursively (HNodeLens typeVars) t) =>
    t # UVarOf m ->
    StateT (typeVars # Binding, [m ()]) m (t # UVar)
saveBody =
    htraverse
        ( Proxy @(Unify m) #*#
            Proxy @(Recursively (HNodeLens typeVars)) #>
                saveVar
        )
        \\ recurse (Proxy @(Unify m t))
        \\ recursively (Proxy @(HNodeLens typeVars t))

-- | Serialize the state of unification for
-- the unification variables in a given value,
-- and transform the value's unification variables
-- to their serialized identifiers.
save ::
    (Unify m t, Recursively (HNodeLens typeVars) t) =>
    t # UVarOf m ->
    StateT (typeVars # Binding) m (t # UVar)
save collection =
    StateT $
        \dstState ->
            do
                (r, (finalState, recover)) <- runStateT (saveBody collection) (dstState, [])
                (r, finalState) <$ sequence_ recover
