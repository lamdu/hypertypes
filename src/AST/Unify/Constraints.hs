module AST.Unify.Constraints
    ( TypeConstraints(..)
    , MonadScopeConstraints(..)
    , TypeConstraintsOf
    ) where

import Algebra.PartialOrd (PartialOrd(..))
import AST (Knot)
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

type family TypeConstraintsOf (ast :: Knot -> Type)
