{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, FlexibleContexts #-}

module AST.Unify.Occurs
    ( occursCheck
    , -- Helper used for fused occurs-check in unification and apply bindings
      occursError
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import AST.Class.Recursive (recursiveChildren_)
import AST.Unify.Error (UnifyError(..))
import AST.Unify.Lookup (semiPruneLookup)
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..))
import AST.Unify.Term (UTerm(..), UTermBody(..), uBody)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

occursError ::
    Unify m t =>
    Tree (UVarOf m) t -> Tree (UTermBody (UVarOf m)) t -> m a
occursError v (UTermBody c b) =
    do
        q <- newQuantifiedVariable c
        bindVar binding v (UResolved (_Pure . quantifiedVar # q))
        unifyError (Occurs (quantifiedVar # q) b)

{-# INLINE occursCheck #-}
occursCheck ::
    forall m t. Recursive (Unify m) t =>
    Tree (UVarOf m) t -> m ()
occursCheck v0 =
    semiPruneLookup v0
    >>=
    \(v1, x) ->
    case x of
    UResolving t -> occursError v1 t
    UResolved{} -> pure ()
    UUnbound{} -> pure ()
    USkolem{} -> pure ()
    UTerm b ->
        case (mMapLeafK :: Maybe (Tree t Pure -> Tree t Pure)) of
        Just{} -> pure () -- no children to check!
        Nothing ->
            do
                bindVar binding v1 (UResolving b)
                recursiveChildren_ (Proxy :: Proxy (Unify m)) occursCheck
                    (b ^. uBody)
                bindVar binding v1 (UTerm b)
    UToVar{} -> error "lookup not expected to result in var (in occursCheck)"
    UConverted{} -> error "conversion state not expected in occursCheck"
    UInstantiated{} -> error "occursCheck during instantiation"
