{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, FlexibleContexts #-}

module AST.Unify.Apply
    ( applyBindings
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import AST.Unify.Lookup (semiPruneLookup)
import AST.Unify.Occurs (occursError)
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..))
import AST.Unify.Term (UTerm(..), uBody)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

{-# INLINE applyBindings #-}
applyBindings ::
    forall m t. Recursive (Unify m) t =>
    Tree (UVarOf m) t -> m (Tree Pure t)
applyBindings v0 =
    semiPruneLookup v0
    >>=
    \(v1, x) ->
    let result r = r <$ bindVar binding v1 (UResolved r)
        quantify c =
            newQuantifiedVariable c <&> (quantifiedVar #) <&> (_Pure #)
            >>= result
    in
    case x of
    UResolving t -> occursError v1 t
    UResolved t -> pure t
    UUnbound c -> quantify c
    USkolem c -> quantify c
    UTerm b ->
        case leafExpr of
        Just f -> _Pure # f (b ^. uBody) & pure
        Nothing ->
            do
                bindVar binding v1 (UResolving b)
                recursiveChildren (Proxy :: Proxy (Unify m)) applyBindings
                    (b ^. uBody)
            <&> (_Pure #)
            >>= result
    UToVar{} -> error "lookup not expected to result in var"
    UConverted{} -> error "conversion state not expected in applyBindings"
    UInstantiated{} -> error "applyBindings during instantiation"
