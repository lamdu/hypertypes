-- | Occurs check (check whether unification terms recursively contains themselves)

module Hyper.Unify.Occurs
    ( occursCheck
    , -- Helper used for fused occurs-check in unification and apply bindings
      occursError
    ) where

import Control.Lens.Operators
import Control.Monad (unless, when)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.State (execStateT, get, put)
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import Hyper
import Hyper.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import Hyper.Unify.Error (UnifyError(..))
import Hyper.Unify.Lookup (semiPruneLookup)
import Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..))
import Hyper.Unify.Term (UTerm(..), UTermBody(..), uBody)

import Prelude.Compat

-- | Format and throw an occurs check error
occursError ::
    Unify m t =>
    Tree (UVarOf m) t -> Tree (UTermBody (UVarOf m)) t -> m a
occursError v (UTermBody c b) =
    do
        q <- newQuantifiedVariable c
        bindVar binding v (UResolved (_Pure . quantifiedVar # q))
        unifyError (Occurs (quantifiedVar # q) b)

-- | Occurs check
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
        withDict (unifyRecursive (Proxy @m) (Proxy @t)) $
        traverseK_
        ( Proxy @(Unify m) #>
            \c ->
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
