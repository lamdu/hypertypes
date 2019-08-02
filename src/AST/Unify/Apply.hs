{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

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
import Control.Monad (unless)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.State (runStateT, get, put)
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

import Prelude.Compat

{-# INLINE applyBindings #-}
applyBindings ::
    forall m t.
    Recursively (Unify m) t =>
    Tree (UVarOf m) t ->
    m (Tree Pure t)
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
        do
            (r, anyChild) <-
                withDict (recursive @(Unify m) @t) $
                traverseKWith (Proxy @'[Recursively (Unify m)])
                ( \c ->
                    do
                        get >>= lift . (`unless` bindVar binding v1 (UResolving b))
                        put True
                        applyBindings c & lift
                ) (b ^. uBody)
                & (`runStateT` False)
            _Pure # r & if anyChild then result else pure
    UToVar{} -> error "lookup not expected to result in var"
    UConverted{} -> error "conversion state not expected in applyBindings"
    UInstantiated{} -> error "applyBindings during instantiation"
