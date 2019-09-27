-- | Resolve terms from unification variables.

module Hyper.Unify.Apply
    ( applyBindings
    ) where

import Control.Lens.Operators
import Control.Monad (unless)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.State (runStateT, get, put)
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import Hyper
import Hyper.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import Hyper.Unify.Lookup (semiPruneLookup)
import Hyper.Unify.Occurs (occursError)
import Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..))
import Hyper.Unify.Term (UTerm(..), uBody)

import Prelude.Compat

-- | Resolve a term from a unification variable.
--
-- Note that this must be done after
-- all unifications involving the term and its children are done,
-- as it replaces unification state with cached resolved terms.
{-# INLINE applyBindings #-}
applyBindings ::
    forall m t.
    Unify m t =>
    Tree (UVarOf m) t ->
    m (Tree Pure t)
applyBindings v0 =
    semiPruneLookup v0
    >>=
    \(v1, x) ->
    let result r = r <$ bindVar binding v1 (UResolved r)
        quantify c =
            newQuantifiedVariable c <&> (_Pure . quantifiedVar #)
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
                withDict (unifyRecursive (Proxy @m) (Proxy @t)) $
                htraverse
                ( Proxy @(Unify m) #>
                    \c ->
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
