{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Class.Infer.ScopeLevel
    ( MonadLevel(..)
    , QuantificationScope(..), _QuantificationScope
    ) where

import Algebra.Lattice (JoinSemiLattice(..))
import Algebra.PartialOrd (PartialOrd(..))
import Control.Lens (makePrisms)

import Prelude.Compat

class Monad m => MonadLevel m where
    localLevel :: m a -> m a

newtype QuantificationScope = QuantificationScope Int
    deriving (Eq, Show)
makePrisms ''QuantificationScope

instance PartialOrd QuantificationScope where
    QuantificationScope x `leq` QuantificationScope y = x >= y

instance JoinSemiLattice QuantificationScope where
    QuantificationScope x \/ QuantificationScope y = QuantificationScope (min x y)

instance Semigroup QuantificationScope where
    (<>) = (\/)

instance Monoid QuantificationScope where
    mempty = QuantificationScope maxBound
