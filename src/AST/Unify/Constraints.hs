{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DefaultSignatures, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, TypeOperators, ScopedTypeVariables, UndecidableInstances #-}

module AST.Unify.Constraints
    ( TypeConstraints(..)
    , HasTypeConstraints(..)
    , TypeConstraintsAre
    , MonadScopeConstraints(..)
    ) where

import Algebra.PartialOrd (PartialOrd(..))
import AST
import AST.Class.Combinators (traverseKWith)
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class (PartialOrd c, Semigroup c) => TypeConstraints c where
    -- | Remove scope constraints
    --
    -- When generalizing unification variables into universally
    -- quantified variables, and then into fresh unification variables
    -- upon instantiation, some constraints need to be carried over,
    -- and the "scope" constraints need to be erased.
    generalizeConstraints :: c -> c

    toScopeConstraints :: c -> c

class
    TypeConstraints (TypeConstraintsOf ast) =>
    HasTypeConstraints (ast :: Knot -> *) where

    type TypeConstraintsOf ast

    -- | Verify constraints on the ast and apply the given child
    -- verifier on children
    verifyConstraints ::
        ( Applicative m
        , KTraversable ast
        , KLiftConstraint (NodeTypesOf ast) childOp
        ) =>
        Proxy childOp ->
        TypeConstraintsOf ast ->
        (TypeConstraintsOf ast -> m ()) ->
        (forall child. childOp child => TypeConstraintsOf child -> Tree p child -> m (Tree q child)) ->
        Tree ast p ->
        m (Tree ast q)
    -- | A default implementation for when the verification only needs
    -- to propagate the unchanged constraints to the direct AST
    -- children
    {-# INLINE verifyConstraints #-}
    default verifyConstraints ::
        forall m childOp p q.
        ( KLiftConstraint (NodeTypesOf ast) (TypeConstraintsAre (TypeConstraintsOf ast))
        , Applicative m
        , KTraversable ast
        , KLiftConstraint (NodeTypesOf ast) childOp
        ) =>
        Proxy childOp ->
        TypeConstraintsOf ast ->
        (TypeConstraintsOf ast -> m ()) ->
        (forall child. childOp child => TypeConstraintsOf child -> Tree p child -> m (Tree q child)) ->
        Tree ast p ->
        m (Tree ast q)
    verifyConstraints _ constraints _ update =
        withDict (hasNodes (Proxy :: Proxy ast)) $
        traverseKWith (Proxy :: Proxy [childOp, TypeConstraintsAre (TypeConstraintsOf ast)])
        (update constraints)

class TypeConstraintsOf ast ~ constraints => TypeConstraintsAre constraints ast
instance TypeConstraintsOf ast ~ constraints => TypeConstraintsAre constraints ast

class Monad m => MonadScopeConstraints c m where
    scopeConstraints :: m c
