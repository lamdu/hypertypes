{-# LANGUAGE DefaultSignatures #-}

module AST.Unify.Binding.Save
    ( Savable(..), save
    ) where

import           AST
import           AST.Class.Has (HasChild(..))
import           AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           AST.Unify.Binding (Binding, _Binding, UVar(..))
import           AST.Unify.Term (UTerm(..), uBody)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..))
import           Data.Constraint (Dict(..), withDict)
import           Data.Proxy (Proxy(..))
import qualified Data.Sequence as Sequence

import           Prelude.Compat

class (Unify m t, HasChild typeVars t) => Savable m typeVars t where
    savableRecursive ::
        Proxy m -> Proxy typeVars -> Proxy t -> Dict (NodesConstraint t (Savable m typeVars))
    {-# INLINE savableRecursive #-}
    default savableRecursive ::
        NodesConstraint t (Savable m typeVars) =>
        Proxy m -> Proxy typeVars -> Proxy t -> Dict (NodesConstraint t (Savable m typeVars))
    savableRecursive _ _ _ = Dict

saveUTerm ::
    forall m typeVars t.
    Savable m typeVars t =>
    Tree (UTerm (UVarOf m)) t ->
    StateT (Tree typeVars Binding, [m ()]) m (Tree (UTerm UVar) t)
saveUTerm (UUnbound c) = UUnbound c & pure
saveUTerm (USkolem c) = USkolem c & pure
saveUTerm (UToVar v) = saveVar v <&> UToVar
saveUTerm (UTerm u) = uBody saveBody u <&> UTerm
saveUTerm UInstantiated{} = error "converting bindings during instantiation"
saveUTerm UResolving{} = error "converting bindings after resolution"
saveUTerm UResolved{} = error "converting bindings after resolution"
saveUTerm UConverted{} = error "converting variable again"

saveVar ::
    Savable m typeVars t =>
    Tree (UVarOf m) t ->
    StateT (Tree typeVars Binding, [m ()]) m (Tree UVar t)
saveVar v =
    lookupVar binding v & lift
    >>=
    \case
    UConverted i -> pure (UVar i)
    srcBody ->
        do
            pb <- Lens.use (Lens._1 . getChild)
            let r = pb ^. _Binding & Sequence.length
            UConverted r & bindVar binding v & lift
            Lens._2 %= (<> [bindVar binding v srcBody])
            dstBody <- saveUTerm srcBody
            Lens._1 . getChild .= (pb & _Binding %~ (Sequence.|> dstBody))
            UVar r & pure

saveBody ::
    forall m typeVars t.
    Savable m typeVars t =>
    Tree t (UVarOf m) ->
    StateT (Tree typeVars Binding, [m ()]) m (Tree t UVar)
saveBody =
    withDict (savableRecursive (Proxy @m) (Proxy @typeVars) (Proxy @t)) $
    traverseKWith (Proxy @(Savable m typeVars)) saveVar

save ::
    Savable m typeVars t =>
    Tree t (UVarOf m) ->
    StateT (Tree typeVars Binding) m (Tree t UVar)
save collection =
    StateT $
    \dstState ->
    do
        (r, (finalState, recover)) <- runStateT (saveBody collection) (dstState, [])
        (r, finalState) <$ sequence_ recover
