{-# LANGUAGE NoImplicitPrelude, TypeFamilies, LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, BangPatterns #-}

module AST.Unify
    ( module AST.Class.Unify
    , module AST.Unify.Constraints
    , module AST.Unify.Error
    , module AST.Unify.QuantifiedVar
    , applyBindings, unify
    , semiPruneLookup
    , newUnbound, newTerm, unfreeze

    , -- Exported for SPECIALIZE pragmas
      updateConstraints, updateTermConstraints
    ) where

import Algebra.PartialOrd (PartialOrd(..))
import Algebra.Lattice (JoinSemiLattice(..))
import AST
import AST.Class.Recursive (wrapM)
import AST.Class.Unify (Unify(..), UVar, BindingDict(..))
import AST.Class.ZipMatch (zipMatchWithA)
import AST.Unify.Constraints (TypeConstraints(..), HasTypeConstraints(..), MonadScopeConstraints(..))
import AST.Unify.Error (UnifyError(..))
import AST.Unify.Term (UTerm(..), UTermBody(..), uConstraints, uBody)
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..), QVarHasInstance)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- Names modeled after unification-fd

{-# INLINE newUnbound #-}
newUnbound :: Unify m t => m (Tree (UVar m) t)
newUnbound = scopeConstraints >>= newVar binding . UUnbound

{-# INLINE newTerm #-}
newTerm :: Unify m t => Tree t (UVar m) -> m (Tree (UVar m) t)
newTerm x = scopeConstraints >>= newVar binding . UTerm . (`UTermBody` x)

-- | Embed a pure term as a unification term.
unfreeze ::
    forall m t.
    Recursive (Unify m) t =>
    Tree Pure t -> m (Tree (UVar m) t)
unfreeze = wrapM (Proxy :: Proxy (Unify m)) newTerm

-- look up a variable, and return last variable pointing to result.
-- prune all variable on way to last variable (path-compression ala union-find)
{-# INLINE semiPruneLookup #-}
semiPruneLookup ::
    Unify m t =>
    Tree (UVar m) t ->
    m (Tree (UVar m) t, Tree (UTerm (UVar m)) t)
semiPruneLookup v0 =
    lookupVar binding v0
    >>=
    \case
    UVar v1 ->
        do
            (v, r) <- semiPruneLookup v1
            bindVar binding v0 (UVar v)
            pure (v, r)
    t -> pure (v0, t)

-- TODO: implement when need / better understand motivations for -
-- occursIn, seenAs, getFreeVars, freshen, equals, equiv

occursError ::
    Unify m t =>
    Tree (UVar m) t -> Tree (UTermBody (UVar m)) t -> m (Tree Pure t)
occursError v (UTermBody c b) =
    do
        q <- newQuantifiedVariable c
        let r = quantifiedVar # q
        bindVar binding v (UResolved (Pure r))
        Pure r <$ unifyError (Occurs (quantifiedVar # q) b)

{-# INLINE applyBindings #-}
applyBindings ::
    forall m t. Recursive (Unify m) t => Tree (UVar m) t -> m (Tree Pure t)
applyBindings v0 =
    semiPruneLookup v0
    >>=
    \(v1, x) ->
    let result r = r <$ bindVar binding v1 (UResolved r)
        quantify c =
            newQuantifiedVariable c <&> (quantifiedVar #) <&> Pure
            >>= result
    in
    case x of
    UResolving t -> occursError v1 t
    UResolved t -> pure t
    UUnbound c -> quantify c
    USkolem c -> quantify c
    UTerm b ->
        case leafExpr of
        Just f -> b ^. uBody & f & Pure & pure
        Nothing ->
            do
                bindVar binding v1 (UResolving b)
                recursiveChildren (Proxy :: Proxy (Unify m)) applyBindings
                    (b ^. uBody)
            <&> Pure
            >>= result
    UVar{} -> error "lookup not expected to result in var"
    UConverted{} -> error "conversion state not expected in applyBindings"
    UInstantiated{} -> error "applyBindings during instantiation"

{-# INLINE updateConstraints #-}
updateConstraints ::
    Recursive (Unify m) t =>
    TypeConstraintsOf t -> Tree (UVar m) t -> m (Tree (UVar m) t)
updateConstraints !newConstraints var =
    do
        (v1, x) <- semiPruneLookup var
        case x of
            UUnbound l
                | newConstraints `leq` l -> pure ()
                | otherwise -> bindVar binding v1 (UUnbound newConstraints)
            USkolem l
                | newConstraints `leq` l -> pure ()
                | otherwise -> SkolemEscape v1 & unifyError
            UTerm t -> updateTermConstraints v1 t newConstraints
            UResolving t -> () <$ occursError var t
            _ -> error "This shouldn't happen in unification stage"
        pure v1

{-# INLINE updateTermConstraints #-}
updateTermConstraints ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UVar m) t -> Tree (UTermBody (UVar m)) t -> TypeConstraintsOf t -> m ()
updateTermConstraints v t newConstraints
    | newConstraints `leq` (t ^. uConstraints) = pure ()
    | otherwise =
        withDict (recursive :: RecursiveDict (Unify m) t) $
        do
            bindVar binding v (UResolving t)
            verifyConstraints (Proxy :: Proxy (Recursive (Unify m))) newConstraints
                (unifyError . ConstraintsViolation (t ^. uBody))
                updateConstraints
                (t ^. uBody)
                >>= bindVar binding v . UTerm . UTermBody newConstraints

-- Note on usage of `semiPruneLookup`:
--   Variables are pruned to point to other variables rather than terms,
--   yielding comparison of (sometimes equal) variables,
--   rather than recursively unifying the terms that they would prune to.
{-# INLINE unify #-}
unify ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UVar m) t -> Tree (UVar m) t -> m (Tree (UVar m) t)
unify x0 y0
    | x0 == y0 = pure x0
    | otherwise =
        go x0 y0 unbound (\x1 !xt -> go y0 x1 (bindToTerm x1 xt) (unifyTerms x1 xt))
    where
        unifyTerms x1 xt y1 yt =
            withDict (recursive :: RecursiveDict (Unify m) t) $
            do
                bindVar binding y1 (UVar x1)
                zipMatchWithA (Proxy :: Proxy (Recursive (Unify m))) unify (xt ^. uBody) (yt ^. uBody)
                    & fromMaybe (xt ^. uBody <$ structureMismatch xt yt)
                    >>= bindVar binding x1 . UTerm . UTermBody (xt ^. uConstraints \/ yt ^. uConstraints)
                pure x1
        bindToTerm dstVar dstTerm var level =
            do
                bindVar binding var (UVar dstVar)
                updateTermConstraints var dstTerm level
                pure dstVar
        unbound var level =
            do
                r <- updateConstraints level y0
                r <$ bindVar binding var (UVar r)
        go var !other onUnbound onTerm =
            semiPruneLookup var
            >>=
            \case
            (v1, _) | v1 == other -> pure other
            (v1, USkolem{}) -> other <$ unifyError (SkolemUnified v1 other)
            (v1, UUnbound level) -> onUnbound v1 level
            (v1, UTerm t) -> onTerm v1 t
            (_, _) -> error "This shouldn't happen in unification stage"
