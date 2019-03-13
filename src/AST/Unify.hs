{-# LANGUAGE NoImplicitPrelude, TypeFamilies, LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, BangPatterns #-}

module AST.Unify
    ( module AST.Class.Unify
    , module AST.Unify.Constraints
    , module AST.Unify.Error
    , module AST.Unify.QuantifiedVar
    , applyBindings, unify
    , semiPruneLookup
    , newUnbound, newTerm, unfreeze, occursError

    , -- Exported for SPECIALIZE pragmas
      updateConstraints, updateTermConstraints, unifyUTerms, unifyUnbound
    ) where

import Algebra.PartialOrd (PartialOrd(..))
import Algebra.Lattice (JoinSemiLattice(..))
import AST
import AST.Class.Recursive (wrapM)
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
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
newUnbound :: Unify m t => m (Tree (UVarOf m) t)
newUnbound = scopeConstraints >>= newVar binding . UUnbound

{-# INLINE newTerm #-}
newTerm :: Unify m t => Tree t (UVarOf m) -> m (Tree (UVarOf m) t)
newTerm x = scopeConstraints >>= newVar binding . UTerm . (`UTermBody` x)

-- | Embed a pure term as a unification term.
unfreeze ::
    forall m t.
    Recursive (Unify m) t =>
    Tree Pure t -> m (Tree (UVarOf m) t)
unfreeze = wrapM (Proxy :: Proxy (Unify m)) newTerm

-- look up a variable, and return last variable pointing to result.
-- prune all variable on way to last variable (path-compression ala union-find)
{-# INLINE semiPruneLookup #-}
semiPruneLookup ::
    Unify m t =>
    Tree (UVarOf m) t ->
    m (Tree (UVarOf m) t, Tree (UTerm (UVarOf m)) t)
semiPruneLookup v0 =
    lookupVar binding v0
    >>=
    \case
    UToVar v1 ->
        do
            (v, r) <- semiPruneLookup v1
            bindVar binding v0 (UToVar v)
            pure (v, r)
    t -> pure (v0, t)

-- TODO: implement when need / better understand motivations for -
-- occursIn, seenAs, getFreeVars, freshen, equals, equiv

occursError ::
    Unify m t =>
    Tree (UVarOf m) t -> Tree (UTermBody (UVarOf m)) t -> m (Tree Pure t)
occursError v (UTermBody c b) =
    do
        q <- newQuantifiedVariable c
        let r = quantifiedVar # q
        bindVar binding v (UResolved (Pure r))
        Pure r <$ unifyError (Occurs (quantifiedVar # q) b)

{-# INLINE applyBindings #-}
applyBindings ::
    forall m t. Recursive (Unify m) t => Tree (UVarOf m) t -> m (Tree Pure t)
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
    UToVar{} -> error "lookup not expected to result in var"
    UConverted{} -> error "conversion state not expected in applyBindings"
    UInstantiated{} -> error "applyBindings during instantiation"

{-# INLINE updateConstraints #-}
updateConstraints ::
    Recursive (Unify m) t =>
    TypeConstraintsOf t ->
    (Tree (UVarOf m) t, Tree (UTerm (UVarOf m)) t) ->
    m ()
updateConstraints !newConstraints (v1, x) =
    case x of
    UUnbound l
        | newConstraints `leq` l -> pure ()
        | otherwise -> bindVar binding v1 (UUnbound newConstraints)
    USkolem l
        | newConstraints `leq` l -> pure ()
        | otherwise -> SkolemEscape v1 & unifyError
    UTerm t -> updateTermConstraints v1 t newConstraints
    UResolving t -> () <$ occursError v1 t
    _ -> error "This shouldn't happen in unification stage"

{-# INLINE updateTermConstraints #-}
updateTermConstraints ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UVarOf m) t -> Tree (UTermBody (UVarOf m)) t -> TypeConstraintsOf t -> m ()
updateTermConstraints v t newConstraints
    | newConstraints `leq` (t ^. uConstraints) = pure ()
    | otherwise =
        withDict (recursive :: RecursiveDict (Unify m) t) $
        do
            bindVar binding v (UResolving t)
            verifyConstraints (Proxy :: Proxy (Recursive (Unify m))) newConstraints
                (unifyError . ConstraintsViolation (t ^. uBody))
                f
                (t ^. uBody)
                >>= bindVar binding v . UTerm . UTermBody newConstraints
    where
        f !c var =
            do
                (v1, x) <- semiPruneLookup var
                v1 <$ updateConstraints c (v1, x)

-- Note on usage of `semiPruneLookup`:
--   Variables are pruned to point to other variables rather than terms,
--   yielding comparison of (sometimes equal) variables,
--   rather than recursively unifying the terms that they would prune to.
{-# INLINE unify #-}
unify ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UVarOf m) t -> Tree (UVarOf m) t -> m (Tree (UVarOf m) t)
unify x0 y0
    | x0 == y0 = pure x0
    | otherwise =
        semiPruneLookup x0
        >>=
        \case
        (x1, _) | x1 == y0 -> pure x1
        (x1, xu) ->
            semiPruneLookup y0
            >>=
            \case
            (y1, _) | x1 == y1 -> pure x1
            y -> unifyUTerms (x1, xu) y

{-# INLINE unifyUnbound #-}
unifyUnbound ::
    Recursive (Unify m) t =>
    (Tree (UVarOf m) t, TypeConstraintsOf t) ->
    (Tree (UVarOf m) t, Tree (UTerm (UVarOf m)) t) ->
    m (Tree (UVarOf m) t)
unifyUnbound (xv, level) (yv, yt) =
    do
        updateConstraints level (yv, yt)
        yv <$ bindVar binding xv (UToVar yv)

{-# INLINE unifyUTerms #-}
unifyUTerms ::
    forall m t.
    Recursive (Unify m) t =>
    (Tree (UVarOf m) t, Tree (UTerm (UVarOf m)) t) ->
    (Tree (UVarOf m) t, Tree (UTerm (UVarOf m)) t) ->
    m (Tree (UVarOf m) t)
unifyUTerms (xv, UUnbound level) y = unifyUnbound (xv, level) y
unifyUTerms x (yv, UUnbound level) = unifyUnbound (yv, level) x
unifyUTerms (xv, USkolem{}) (yv, _) = xv <$ unifyError (SkolemUnified xv yv)
unifyUTerms (xv, _) (yv, USkolem{}) = yv <$ unifyError (SkolemUnified yv xv)
unifyUTerms (xv, UTerm xt) (yv, UTerm yt) =
    withDict (recursive :: RecursiveDict (Unify m) t) $
    do
        bindVar binding yv (UToVar xv)
        zipMatchWithA (Proxy :: Proxy (Recursive (Unify m))) unify (xt ^. uBody) (yt ^. uBody)
            & fromMaybe (xt ^. uBody <$ structureMismatch xt yt)
            >>= bindVar binding xv . UTerm . UTermBody (xt ^. uConstraints \/ yt ^. uConstraints)
        pure xv
unifyUTerms _ _ = error "This shouldn't happen in unification stage"
