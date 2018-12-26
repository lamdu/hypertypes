{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Unify.QuantificationScope
    ( QuantificationScope(..), _QuantificationScope
    ) where

import Algebra.Lattice (JoinSemiLattice(..))
import Algebra.PartialOrd (PartialOrd(..))
import Control.Lens (makePrisms)

import Prelude.Compat

newtype QuantificationScope = QuantificationScope Int
    deriving (Eq, Show)
makePrisms ''QuantificationScope

instance PartialOrd QuantificationScope where
    QuantificationScope x `leq` QuantificationScope y = x >= y

instance JoinSemiLattice QuantificationScope where
    QuantificationScope x \/ QuantificationScope y = QuantificationScope (min x y)