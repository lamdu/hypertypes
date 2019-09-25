-- | Load serialized a binding state to 'Control.Monad.ST.ST' based bindings

{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Hyper.Unify.Binding.ST.Load
    ( load
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.ST.Class (MonadST(..))
import           Data.Array.ST (STArray, newArray, readArray, writeArray)
import           Data.Constraint (withDict)
import           Data.Proxy (Proxy(..))
import qualified Data.Sequence as Sequence
import           Hyper
import           Hyper.Class.Has (HasChild(..))
import           Hyper.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           Hyper.Recurse
import           Hyper.Unify.Binding (Binding(..), _Binding, UVar(..))
import           Hyper.Unify.Binding.ST (STUVar)
import           Hyper.Unify.Term (UTerm(..), uBody)

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
    , Unify m t
    , Recursively (HasChild typeVars) t
    ) =>
    Tree typeVars Binding -> Tree typeVars (ConvertState (World m)) ->
    Tree (UTerm UVar) t -> m (Tree (UTerm (STUVar (World m))) t)
loadUTerm _ _ (UUnbound c) = UUnbound c & pure
loadUTerm _ _ (USkolem c) = USkolem c & pure
loadUTerm src conv (UToVar v) = loadVar src conv v <&> UToVar
loadUTerm src conv (UTerm u) = uBody (loadBody src conv) u <&> UTerm
loadUTerm _ _ UResolving{} = error "converting bindings after resolution"
loadUTerm _ _ UResolved{} = error "converting bindings after resolution"
loadUTerm _ _ UConverted{} = error "loading while saving?"
loadUTerm _ _ UInstantiated{} = error "loading during instantiation"

loadVar ::
    forall m t typeVars.
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , Unify m t
    , Recursively (HasChild typeVars) t
    ) =>
    Tree typeVars Binding -> Tree typeVars (ConvertState (World m)) ->
    Tree UVar t -> m (Tree (STUVar (World m)) t)
loadVar src conv (UVar v) =
    withDict (recursively (Proxy @(HasChild typeVars t))) $
    let tConv = conv ^. getChild . _ConvertState
    in
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

loadBody ::
    forall m typeVars t.
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , Unify m t
    , Recursively (HasChild typeVars) t
    ) =>
    Tree typeVars Binding -> Tree typeVars (ConvertState (World m)) ->
    Tree t UVar -> m (Tree t (STUVar (World m)))
loadBody src conv =
    withDict (recurse (Proxy @(Unify m t))) $
    withDict (recursively (Proxy @(HasChild typeVars t))) $
    traverseH
    ( Proxy @(Unify m) #*# Proxy @(Recursively (HasChild typeVars))
        #> loadVar src conv
    )

-- | Load a given serialized unification
-- and a value with serialized unification variable identifiers
-- to a value with 'Control.Monad.ST.ST' unification variables.
load ::
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , HTraversable typeVars
    , Unify m t
    , Recursively (HasChild typeVars) t
    ) =>
    Tree typeVars Binding -> Tree t UVar -> m (Tree t (STUVar (World m)))
load src collection =
    do
        conv <- traverseH (const makeConvertState) src
        loadBody src conv collection
