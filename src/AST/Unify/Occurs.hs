module AST.Unify.Occurs
    ( occursCheck
    , -- Helper used for fused occurs-check in unification and apply bindings
      occursError
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import AST.Unify.Error (UnifyError(..))
import AST.Unify.Lookup (semiPruneLookup)
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..))
import AST.Unify.Term (UTerm(..), UTermBody(..), uBody)
import Control.Lens.Operators
import Control.Monad (unless, when)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.State (execStateT, get, put)
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
    forall m t.
    Unify m t =>
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
        unifyRecursive (Proxy @m) (Proxy @t) $
        traverseKWith_ (Proxy @(Unify m))
        ( \c ->
            do
                get >>= lift . (`unless` bindVar binding v1 (UResolving b))
                put True
                occursCheck c & lift
        ) (b ^. uBody)
        & (`execStateT` False)
        >>= (`when` bindVar binding v1 (UTerm b))
    UToVar{} -> error "lookup not expected to result in var (in occursCheck)"
    UConverted{} -> error "conversion state not expected in occursCheck"
    UInstantiated{} -> error "occursCheck during instantiation"
