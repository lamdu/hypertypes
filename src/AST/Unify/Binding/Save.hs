{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, FlexibleContexts, LambdaCase #-}
{-# LANGUAGE TypeOperators, ConstraintKinds #-}

module AST.Unify.Binding.Save
    ( save
    ) where

import           AST
import           AST.Class.Combinators (And)
import           AST.Class.HasChild (HasChild(..))
import           AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           AST.Unify.Binding (Binding, _Binding)
import           AST.Unify.Term (UTerm(..), uBody)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..))
import           Data.Constraint (withDict)
import           Data.Functor.Const (Const(..))
import           Data.Proxy (Proxy(..))
import qualified Data.Sequence as Sequence

import           Prelude.Compat

type Deps m typeVars = Unify m `And` HasChild typeVars

saveUTerm ::
    forall m typeVars t.
    Recursive (Deps m typeVars) t =>
    Tree (UTerm (UVarOf m)) t ->
    StateT (Tree typeVars Binding, [m ()]) m (Tree (UTerm (Const Int)) t)
saveUTerm (UUnbound c) = UUnbound c & pure
saveUTerm (USkolem c) = USkolem c & pure
saveUTerm (UVar v) = saveVar v <&> UVar
saveUTerm (UTerm u) =
    withDict (recursive :: RecursiveDict (Deps m typeVars) t) $
    uBody saveBody u <&> UTerm
saveUTerm UInstantiated{} = error "converting bindings during instantiation"
saveUTerm UResolving{} = error "converting bindings after resolution"
saveUTerm UResolved{} = error "converting bindings after resolution"
saveUTerm UConverted{} = error "converting variable again"

saveVar ::
    Recursive (Deps m typeVars) t =>
    Tree (UVarOf m) t ->
    StateT (Tree typeVars Binding, [m ()]) m (Tree (Const Int) t)
saveVar v =
    lookupVar binding v & lift
    >>=
    \case
    UConverted i -> pure (Const i)
    srcBody ->
        do
            pb <- Lens.use (Lens._1 . getChild)
            let r = pb ^. _Binding & Sequence.length
            UConverted r & bindVar binding v & lift
            Lens._2 %= (<> [bindVar binding v srcBody])
            dstBody <- saveUTerm srcBody
            Lens._1 . getChild .= (pb & _Binding %~ (Sequence.|> dstBody))
            Const r & pure

saveBody ::
    forall m typeVars t.
    ( Monad m
    , ChildrenWithConstraint t (Recursive (Deps m typeVars))
    ) =>
    Tree t (UVarOf m) ->
    StateT (Tree typeVars Binding, [m ()]) m (Tree t (Const Int))
saveBody =
    children (Proxy :: Proxy (Recursive (Deps m typeVars))) saveVar

save ::
    ( Monad m
    , ChildrenWithConstraint t (Recursive (Deps m typeVars))
    ) =>
    Tree t (UVarOf m) ->
    StateT (Tree typeVars Binding) m (Tree t (Const Int))
save collection =
    StateT $
    \dstState ->
    do
        (r, (finalState, recover)) <- runStateT (saveBody collection) (dstState, [])
        (r, finalState) <$ sequence_ recover
