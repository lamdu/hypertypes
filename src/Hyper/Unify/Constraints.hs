{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

-- | A class for constraints for unification variables
module Hyper.Unify.Constraints
    ( TypeConstraints (..)
    , HasTypeConstraints (..)
    , WithConstraint (..)
    , wcConstraint
    , wcBody
    ) where

import Algebra.PartialOrd (PartialOrd (..))
import Data.Kind (Type)
import Hyper (GetHyperType, HyperType, type (#))

import Hyper.Internal.Prelude

-- | A class for constraints for unification variables.
class (PartialOrd c, Monoid c) => TypeConstraints c where
    -- | Remove scope constraints.
    --
    -- When generalizing unification variables into universally
    -- quantified variables, and then into fresh unification variables
    -- upon instantiation, some constraints need to be carried over,
    -- and the "scope" constraints need to be erased.
    generalizeConstraints :: c -> c

    -- | Remove all constraints other than the scope constraints
    --
    -- Useful for comparing constraints to the current scope constraints
    toScopeConstraints :: c -> c

-- | A class for terms that have constraints.
--
-- A dependency of `Hyper.Class.Unify.Unify`
class
    TypeConstraints (TypeConstraintsOf ast) =>
    HasTypeConstraints (ast :: HyperType)
    where
    type TypeConstraintsOf (ast :: HyperType) :: Type

    -- | Verify constraints on the ast and apply the given child
    -- verifier on children
    verifyConstraints ::
        TypeConstraintsOf ast ->
        ast # h ->
        Maybe (ast # WithConstraint h)

-- | A 'HyperType' to represent a term alongside a constraint.
--
-- Used for 'verifyConstraints'.
data WithConstraint h ast = WithConstraint
    { _wcConstraint :: TypeConstraintsOf (GetHyperType ast)
    , _wcBody :: h ast
    }

makeLenses ''WithConstraint
