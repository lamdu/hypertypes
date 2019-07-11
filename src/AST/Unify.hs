{-# LANGUAGE NoImplicitPrelude, TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, BangPatterns #-}

module AST.Unify
    ( module AST.Class.Unify
    , module AST.Unify.Constraints
    , module AST.Unify.Error
    , module AST.Unify.QuantifiedVar
    , applyBindings, unify
    , newUnbound, newTerm, unfreeze

    , -- Exported for SPECIALIZE pragmas
      updateConstraints, updateTermConstraints, unifyUTerms, unifyUnbound
    ) where

import Algebra.PartialOrd (PartialOrd(..))
import Algebra.Lattice (JoinSemiLattice(..))
import AST
import AST.Class.Recursive (wrapM)
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import AST.Class.ZipMatch (zipMatchWithA)
import AST.Unify.Binding.Lookup (semiPruneLookup)
import AST.Unify.Constraints (TypeConstraints(..), HasTypeConstraints(..), MonadScopeConstraints(..))
import AST.Unify.Error (UnifyError(..))
import AST.Unify.Occurs (occursError)
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..), QVarHasInstance)
import AST.Unify.Term (UTerm(..), UTermBody(..), uConstraints, uBody)
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

-- TODO: implement when need / better understand motivations for -
-- occursIn, seenAs, getFreeVars, freshen, equals, equiv

{-# INLINE applyBindings #-}
applyBindings ::
    forall m t. Recursive (Unify m) t => Tree (UVarOf m) t -> m (Tree Pure t)
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

{-# INLINE updateConstraints #-}
updateConstraints ::
    Recursive (Unify m) t =>
    TypeConstraintsOf t ->
    Tree (UVarOf m) t ->
    Tree (UTerm (UVarOf m)) t ->
    m ()
updateConstraints !newConstraints v x =
    case x of
    UUnbound l
        | newConstraints `leq` l -> pure ()
        | otherwise -> bindVar binding v (UUnbound newConstraints)
    USkolem l
        | newConstraints `leq` l -> pure ()
        | otherwise -> SkolemEscape v & unifyError
    UTerm t -> updateTermConstraints v t newConstraints
    UResolving t -> () <$ occursError v t
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
        {-# INLINE f #-}
        f !c var =
            do
                (v1, x) <- semiPruneLookup var
                v1 <$ updateConstraints c v1 x

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
        do
            (x1, xu) <- semiPruneLookup x0
            if x1 == y0
                then pure x1
                else
                    do
                        (y1, yu) <- semiPruneLookup y0
                        if x1 == y1
                            then pure x1
                            else unifyUTerms x1 xu y1 yu

{-# INLINE unifyUnbound #-}
unifyUnbound ::
    Recursive (Unify m) t =>
    Tree (UVarOf m) t -> TypeConstraintsOf t ->
    Tree (UVarOf m) t -> Tree (UTerm (UVarOf m)) t ->
    m (Tree (UVarOf m) t)
unifyUnbound xv level yv yt =
    do
        updateConstraints level yv yt
        yv <$ bindVar binding xv (UToVar yv)

{-# INLINE unifyUTerms #-}
unifyUTerms ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UVarOf m) t -> Tree (UTerm (UVarOf m)) t ->
    Tree (UVarOf m) t -> Tree (UTerm (UVarOf m)) t ->
    m (Tree (UVarOf m) t)
unifyUTerms xv (UUnbound level) yv yt = unifyUnbound xv level yv yt
unifyUTerms xv xt yv (UUnbound level) = unifyUnbound yv level xv xt
unifyUTerms xv USkolem{} yv _ = xv <$ unifyError (SkolemUnified xv yv)
unifyUTerms xv _ yv USkolem{} = yv <$ unifyError (SkolemUnified yv xv)
unifyUTerms xv (UTerm xt) yv (UTerm yt) =
    withDict (recursive :: RecursiveDict (Unify m) t) $
    do
        bindVar binding yv (UToVar xv)
        zipMatchWithA (Proxy :: Proxy (Recursive (Unify m))) unify (xt ^. uBody) (yt ^. uBody)
            & fromMaybe (xt ^. uBody <$ structureMismatch unify xt yt)
            >>= bindVar binding xv . UTerm . UTermBody (xt ^. uConstraints \/ yt ^. uConstraints)
        pure xv
unifyUTerms _ _ _ _ = error "This shouldn't happen in unification stage"
