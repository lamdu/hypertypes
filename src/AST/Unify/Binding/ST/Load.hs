{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, FlexibleContexts, TemplateHaskell #-}
{-# LANGUAGE LambdaCase, TypeFamilies, TypeOperators #-}

-- | Load state from pure bindings to ST based bindings

module AST.Unify.Binding.ST.Load
    ( load
    ) where

import           AST
import           AST.Class.Combinators (And, NoConstraint)
import           AST.Class.HasChild (HasChild(..))
import           AST.Class.Unify (Unify(..), UVar)
import           AST.Unify.Binding (Binding(..))
import           AST.Unify.Binding.Pure (PureBinding(..), _PureBinding)
import           AST.Unify.Binding.ST (STVar)
import           AST.Unify.Term (UTerm(..), uBody)
import           Control.Lens (makePrisms)
import           Control.Lens.Operators
import           Control.Monad.ST.Class (MonadST(..))
import           Data.Array.ST (STArray, newArray, readArray, writeArray)
import           Data.Constraint (withDict)
import           Data.Functor.Const (Const(..))
import           Data.Proxy (Proxy(..))
import qualified Data.Sequence as Sequence

import           Prelude.Compat

newtype ConvertState s t = ConvertState (STArray s Int (Maybe (STVar s t)))
makePrisms ''ConvertState

makeConvertState :: MonadST m => Tree PureBinding t -> m (Tree (ConvertState (World m)) t)
makeConvertState (PureBinding x) =
    newArray (0, Sequence.length x) Nothing & liftST <&> ConvertState

loadUTerm ::
    forall m typeVars t.
    ( MonadST m
    , UVar m ~ STVar (World m)
    , Recursive (HasChild typeVars `And` Unify m) t
    ) =>
    Tree typeVars PureBinding -> Tree typeVars (ConvertState (World m)) ->
    Tree (UTerm (Const Int)) t -> m (Tree (UTerm (STVar (World m))) t)
loadUTerm _ _ (UUnbound c) = UUnbound c & pure
loadUTerm _ _ (USkolem c) = USkolem c & pure
loadUTerm src conv (UVar v) = loadVar src conv v <&> UVar
loadUTerm src conv (UTerm u) =
    withDict (recursive :: RecursiveDict (HasChild typeVars `And` Unify m) t) $
    uBody (loadBody src conv) u <&> UTerm
loadUTerm _ _ UResolving{} = error "converting bindings after resolution"
loadUTerm _ _ UResolved{} = error "converting bindings after resolution"
loadUTerm _ _ UConverted{} = error "loading while saving?"

loadVar ::
    ( MonadST m
    , UVar m ~ STVar (World m)
    , Recursive (HasChild typeVars `And` Unify m) t
    ) =>
    Tree typeVars PureBinding -> Tree typeVars (ConvertState (World m)) ->
    Tree (Const Int) t -> m (Tree (STVar (World m)) t)
loadVar src conv (Const v) =
    readArray tConv v & liftST
    >>=
    \case
    Just x -> pure x
    Nothing ->
        do
            u <- loadUTerm src conv (Sequence.index (src ^. getChild . _PureBinding) v)
            r <- newVar binding u
            r <$ liftST (writeArray tConv v (Just r))
    where
        tConv = conv ^. getChild . _ConvertState

loadBody ::
    forall m typeVars t.
    ( MonadST m
    , UVar m ~ STVar (World m)
    , ChildrenWithConstraint t (Recursive (HasChild typeVars `And` Unify m))
    ) =>
    Tree typeVars PureBinding -> Tree typeVars (ConvertState (World m)) ->
    Tree t (Const Int) -> m (Tree t (STVar (World m)))
loadBody src conv =
    children
    (Proxy :: Proxy (Recursive (HasChild typeVars `And` Unify m)))
    (loadVar src conv)

load ::
    ( MonadST m
    , UVar m ~ STVar (World m)
    , ChildrenWithConstraint typeVars NoConstraint
    , ChildrenWithConstraint t (Recursive (HasChild typeVars `And` Unify m))
    ) =>
    Tree typeVars PureBinding -> Tree t (Const Int) -> m (Tree t (STVar (World m)))
load src collection =
    do
        conv <- children (Proxy :: Proxy NoConstraint) makeConvertState src
        loadBody src conv collection
