{-# LANGUAGE FlexibleContexts, TemplateHaskell #-}

module AST.Unify.Constraints
    ( TypeConstraints(..)
    , MonadScopeConstraints(..)
    , HasTypeConstraints(..)
    , WithConstraint(..), wcConstraint, wcBody
    ) where

import Algebra.PartialOrd (PartialOrd(..))
import AST (Tree, Knot, RunKnot)
import Control.Lens (makeLenses)
import Data.Kind (Type)

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

class Monad m => MonadScopeConstraints c m where
    scopeConstraints :: m c

class
    TypeConstraints (TypeConstraintsOf ast) =>
    HasTypeConstraints (ast :: Knot -> *) where

    type family TypeConstraintsOf (ast :: Knot -> Type) :: Type

    -- | Verify constraints on the ast and apply the given child
    -- verifier on children
    verifyConstraints ::
        TypeConstraintsOf ast ->
        Tree ast k ->
        Maybe (Tree ast (WithConstraint k))

data WithConstraint k ast = WithConstraint
    { _wcConstraint :: TypeConstraintsOf (RunKnot ast)
    , _wcBody :: k ast
    }
makeLenses ''WithConstraint
