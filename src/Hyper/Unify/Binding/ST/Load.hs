-- | Load serialized a binding state to 'Control.Monad.ST.ST' based bindings

{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

module Hyper.Unify.Binding.ST.Load
    ( load
    ) where

import qualified Control.Lens as Lens
import           Control.Monad.ST.Class (MonadST(..))
import           Data.Array.ST (STArray, newArray, readArray, writeArray)
import qualified Data.Sequence as Sequence
import           Hyper
import           Hyper.Class.Optic (HLens, hLens)
import           Hyper.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           Hyper.Recurse
import           Hyper.Unify.Binding (Binding(..), _Binding, UVar(..))
import           Hyper.Unify.Binding.ST (STUVar)
import           Hyper.Unify.Term (UTerm(..), uBody)

import           Hyper.Internal.Prelude

newtype ConvertState s t = ConvertState (STArray s Int (Maybe (STUVar s t)))
makePrisms ''ConvertState

makeConvertState :: MonadST m => Binding # t -> m (ConvertState (World m) # t)
makeConvertState (Binding x) =
    newArray (0, Sequence.length x) Nothing & liftST <&> ConvertState

loadUTerm ::
    forall m typeVars t.
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , Unify m t
    , Recursively (HLens typeVars) t
    ) =>
    typeVars # Binding -> typeVars # ConvertState (World m) ->
    UTerm UVar # t -> m (UTerm (STUVar (World m)) # t)
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
    , Recursively (HLens typeVars) t
    ) =>
    typeVars # Binding -> typeVars # ConvertState (World m) ->
    UVar # t -> m (STUVar (World m) # t)
loadVar src conv (UVar v) =
    withDict (recursively (Proxy @(HLens typeVars t))) $
    let tConv = conv ^. hLens . _ConvertState
    in
    readArray tConv v & liftST
    >>=
    \case
    Just x -> pure x
    Nothing ->
        do
            u <-
                loadUTerm src conv
                (src ^?! hLens . _Binding . Lens.ix v)
            r <- newVar binding u
            r <$ liftST (writeArray tConv v (Just r))

loadBody ::
    forall m typeVars t.
    ( MonadST m
    , UVarOf m ~ STUVar (World m)
    , Unify m t
    , Recursively (HLens typeVars) t
    ) =>
    typeVars # Binding -> typeVars # ConvertState (World m) ->
    t # UVar -> m (t # STUVar (World m))
loadBody src conv =
    withDict (recurse (Proxy @(Unify m t))) $
    withDict (recursively (Proxy @(HLens typeVars t))) $
    htraverse
    ( Proxy @(Unify m) #*# Proxy @(Recursively (HLens typeVars))
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
    , Recursively (HLens typeVars) t
    ) =>
    typeVars # Binding -> t # UVar -> m (t #STUVar (World m))
load src collection =
    do
        conv <- htraverse (const makeConvertState) src
        loadBody src conv collection
