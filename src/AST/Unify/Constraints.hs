{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module AST.Unify.Constraints
    ( QuantificationScope(..), _QuantificationScope
    , TypeConstraints(..)
    , TypeConstraintsOf, TypeConstraintsAre
    ) where

import Algebra.Lattice (JoinSemiLattice(..))
import Algebra.PartialOrd (PartialOrd(..))
import AST.Knot (Knot)
import Control.Lens (Lens', makePrisms)

import Prelude.Compat

newtype QuantificationScope = QuantificationScope Int
    deriving (Eq, Show)
makePrisms ''QuantificationScope

instance PartialOrd QuantificationScope where
    QuantificationScope x `leq` QuantificationScope y = x >= y

instance JoinSemiLattice QuantificationScope where
    QuantificationScope x \/ QuantificationScope y = QuantificationScope (min x y)

class (PartialOrd c, JoinSemiLattice c) => TypeConstraints c where
    constraintsFromScope :: QuantificationScope -> c
    constraintsScope :: Lens' c QuantificationScope

instance TypeConstraints QuantificationScope where
    constraintsFromScope = id
    constraintsScope = id

type family TypeConstraintsOf (ast :: Knot -> *)

class TypeConstraintsOf ast ~ constraints => TypeConstraintsAre constraints ast
instance TypeConstraintsOf ast ~ constraints => TypeConstraintsAre constraints ast

