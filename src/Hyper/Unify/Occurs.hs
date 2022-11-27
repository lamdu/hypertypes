-- | Occurs check (check whether unification terms recursively contains themselves)

module Hyper.Unify.Occurs
    ( occursCheck
    ) where

import Control.Monad (unless, when)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.State (execStateT, get, put)
import Hyper
import Hyper.Class.Unify (Unify(..), UVarOf, BindingDict(..), semiPruneLookup, occursError)
import Hyper.Unify.Term (UTerm(..), uBody)

import Hyper.Internal.Prelude

-- | Occurs check
{-# INLINE occursCheck #-}
occursCheck ::
    forall m t.
    Unify m t =>
    UVarOf m # t -> m ()
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
        htraverse_
        ( Proxy @(Unify m) #>
            \c ->
            do
                get >>= lift . (`unless` bindVar binding v1 (UResolving b))
                put True
                occursCheck c & lift
        ) (b ^. uBody)
        & (`execStateT` False)
        >>= (`when` bindVar binding v1 (UTerm b))
        \\ unifyRecursive (Proxy @m) (Proxy @t)
    UToVar{} -> error "lookup not expected to result in var (in occursCheck)"
    UConverted{} -> error "conversion state not expected in occursCheck"
    UInstantiated{} -> error "occursCheck during instantiation"
