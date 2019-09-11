{-# LANGUAGE BangPatterns #-}

module AST.Unify
    ( unify
    , module AST.Class.Unify
    , module AST.Unify.Constraints
    , module AST.Unify.Error

    , -- | Exported only for SPECIALIZE pragmas
      updateConstraints, updateTermConstraints, updateTermConstraintsH
    , unifyUTerms, unifyUnbound
    ) where

import Algebra.PartialOrd (PartialOrd(..))
import AST
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import AST.Class.ZipMatch (zipMatchA)
import AST.Unify.Constraints
import AST.Unify.Error (UnifyError(..))
import AST.Unify.Lookup (semiPruneLookup)
import AST.Unify.Occurs (occursError)
import AST.Unify.Term (UTerm(..), UTermBody(..), uConstraints, uBody)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- TODO: implement when need / better understand motivations for -
-- occursIn, seenAs, getFreeVars, freshen, equals, equiv
-- (from unification-fd package)

{-# INLINE updateConstraints #-}
updateConstraints ::
    Unify m t =>
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
    Unify m t =>
    Tree (UVarOf m) t ->
    Tree (UTermBody (UVarOf m)) t ->
    TypeConstraintsOf t ->
    m ()
updateTermConstraints v t newConstraints
    | newConstraints `leq` (t ^. uConstraints) = pure ()
    | otherwise =
        withDict (unifyRecursive (Proxy @m) (Proxy @t)) $
        do
            bindVar binding v (UResolving t)
            case verifyConstraints newConstraints (t ^. uBody) of
                Nothing -> ConstraintsViolation (t ^. uBody) newConstraints & unifyError
                Just prop ->
                    do
                        traverseK_ (Proxy @(Unify m) #> updateTermConstraintsH) prop
                        UTermBody newConstraints (t ^. uBody) & UTerm & bindVar binding v

{-# INLINE updateTermConstraintsH #-}
updateTermConstraintsH ::
    Unify m t =>
    Tree (WithConstraint (UVarOf m)) t ->
    m ()
updateTermConstraintsH (WithConstraint c v0) =
    do
        (v1, x) <- semiPruneLookup v0
        updateConstraints c v1 x

-- | Unification of terms
{-# INLINE unify #-}
unify ::
    forall m t.
    Unify m t =>
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
    Unify m t =>
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
    Unify m t =>
    Tree (UVarOf m) t -> Tree (UTerm (UVarOf m)) t ->
    Tree (UVarOf m) t -> Tree (UTerm (UVarOf m)) t ->
    m (Tree (UVarOf m) t)
unifyUTerms xv (UUnbound level) yv yt = unifyUnbound xv level yv yt
unifyUTerms xv xt yv (UUnbound level) = unifyUnbound yv level xv xt
unifyUTerms xv USkolem{} yv _ = xv <$ unifyError (SkolemUnified xv yv)
unifyUTerms xv _ yv USkolem{} = yv <$ unifyError (SkolemUnified yv xv)
unifyUTerms xv (UTerm xt) yv (UTerm yt) =
    withDict (unifyRecursive (Proxy @m) (Proxy @t)) $
    do
        bindVar binding yv (UToVar xv)
        zipMatchA (Proxy @(Unify m) #> unify) (xt ^. uBody) (yt ^. uBody)
            & fromMaybe (xt ^. uBody <$ structureMismatch unify xt yt)
            >>= bindVar binding xv . UTerm . UTermBody (xt ^. uConstraints <> yt ^. uConstraints)
        pure xv
unifyUTerms _ _ _ _ = error "This shouldn't happen in unification stage"
