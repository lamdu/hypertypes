{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, FlexibleContexts, TemplateHaskell #-}
{-# LANGUAGE LambdaCase, TypeFamilies, TypeOperators #-}

-- | Load state from pure bindings to ST based bindings

module AST.Unify.STBinding.Load
    ( load
    ) where

import           AST.Class.Children (Children(..), ChildrenWithConstraint)
import           AST.Class.Combinators (And)
import           AST.Class.HasChild (HasChild(..))
import           AST.Class.Recursive (Recursive(..), RecursiveDict)
import           AST.Knot (Tree)
import           AST.Unify (Unify(..), Binding(..), UVar)
import           AST.Unify.PureBinding (PureBinding(..), _PureBinding)
import           AST.Unify.STBinding (STVar)
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
    forall m typeVars t.
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
            u <- loadUTerm src conv (Sequence.index tBinding v)
            r <- newVar binding u
            r <$ liftST (writeArray tConv v (Just r))
    where
        tConv = (conv ^. getChild :: Tree (ConvertState (World m)) t) ^. _ConvertState
        tBinding = (src ^. getChild :: Tree PureBinding t) ^. _PureBinding

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
    forall m typeVars t.
    ( MonadST m
    , UVar m ~ STVar (World m)
    , Children typeVars
    , ChildrenWithConstraint t (Recursive (HasChild typeVars `And` Unify m))
    ) =>
    Tree typeVars PureBinding -> Tree t (Const Int) -> m (Tree t (STVar (World m)))
load src collection =
    do
        conv <- childrenNoConstraint makeConvertState src
        loadBody src conv collection
