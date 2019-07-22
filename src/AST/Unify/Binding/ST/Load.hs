{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, FlexibleContexts, TemplateHaskell #-}
{-# LANGUAGE LambdaCase, TypeFamilies, TypeOperators, DataKinds #-}

-- | Load state from pure bindings to ST based bindings

module AST.Unify.Binding.ST.Load
    ( load
    ) where

import           AST
import           AST.Class.Combinators
import           AST.Class.HasChild (HasChild(..))
import           AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           AST.Unify.Binding (Binding(..), _Binding, UVar(..))
import           AST.Unify.Binding.ST (STUVar)
import           AST.Unify.Term (UTerm(..), uBody)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.ST.Class (MonadST(..))
import           Data.Array.ST (STArray, newArray, readArray, writeArray)
import           Data.Constraint (withDict)
import           Data.Proxy (Proxy(..))
import qualified Data.Sequence as Sequence

import           Prelude.Compat

newtype ConvertState s t = ConvertState (STArray s Int (Maybe (STUVar s t)))
Lens.makePrisms ''ConvertState

makeConvertState :: MonadST m => Tree Binding t -> m (Tree (ConvertState (World m)) t)
makeConvertState (Binding x) =
    newArray (0, Sequence.length x) Nothing & liftST <&> ConvertState

loadUTerm ::
    forall m typeVars t.
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , Recursive (HasChild typeVars `And` Unify m) t
    ) =>
    Tree typeVars Binding -> Tree typeVars (ConvertState (World m)) ->
    Tree (UTerm UVar) t -> m (Tree (UTerm (STUVar (World m))) t)
loadUTerm _ _ (UUnbound c) = UUnbound c & pure
loadUTerm _ _ (USkolem c) = USkolem c & pure
loadUTerm src conv (UToVar v) = loadVar src conv v <&> UToVar
loadUTerm src conv (UTerm u) =
    withDict (recursive :: RecursiveDict (HasChild typeVars `And` Unify m) t) $
    uBody (loadBody src conv) u <&> UTerm
loadUTerm _ _ UResolving{} = error "converting bindings after resolution"
loadUTerm _ _ UResolved{} = error "converting bindings after resolution"
loadUTerm _ _ UConverted{} = error "loading while saving?"
loadUTerm _ _ UInstantiated{} = error "loading during instantiation"

loadVar ::
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , Recursive (HasChild typeVars `And` Unify m) t
    ) =>
    Tree typeVars Binding -> Tree typeVars (ConvertState (World m)) ->
    Tree UVar t -> m (Tree (STUVar (World m)) t)
loadVar src conv (UVar v) =
    readArray tConv v & liftST
    >>=
    \case
    Just x -> pure x
    Nothing ->
        do
            u <-
                loadUTerm src conv
                (src ^?! getChild . _Binding . Lens.ix v)
            r <- newVar binding u
            r <$ liftST (writeArray tConv v (Just r))
    where
        tConv = conv ^. getChild . _ConvertState

loadBody ::
    forall m typeVars t.
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , KTraversable t
    , HasChildrenTypes t
    , KLiftConstraint (ChildrenTypesOf t) (Recursive (HasChild typeVars `And` Unify m))
    ) =>
    Tree typeVars Binding -> Tree typeVars (ConvertState (World m)) ->
    Tree t UVar -> m (Tree t (STUVar (World m)))
loadBody src conv =
    withDict (hasChildrenTypes (Proxy :: Proxy t)) $
    traverseKWith
    (Proxy :: Proxy '[Recursive (HasChild typeVars `And` Unify m)])
    (loadVar src conv)

load ::
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , KTraversable typeVars, HasChildrenTypes typeVars
    , KTraversable t, HasChildrenTypes t
    , KLiftConstraint (ChildrenTypesOf t) (Recursive (HasChild typeVars `And` Unify m))
    ) =>
    Tree typeVars Binding -> Tree t UVar -> m (Tree t (STUVar (World m)))
load src collection =
    do
        conv <- traverseK makeConvertState src
        loadBody src conv collection
