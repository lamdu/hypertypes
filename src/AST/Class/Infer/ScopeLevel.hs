{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric #-}

module AST.Class.Infer.ScopeLevel
    ( MonadScopeLevel(..)
    , ScopeLevel(..), _ScopeLevel
    ) where

import           Algebra.Lattice (JoinSemiLattice(..), BoundedJoinSemiLattice(..))
import           Algebra.PartialOrd (PartialOrd(..))
import           Control.DeepSeq (NFData)
import           Data.Binary (Binary)
import           Control.Lens (makePrisms)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

class Monad m => MonadScopeLevel m where
    localLevel :: m a -> m a

newtype ScopeLevel = ScopeLevel Int
    deriving (Eq, Show, Generic)
makePrisms ''ScopeLevel

instance PartialOrd ScopeLevel where
    ScopeLevel x `leq` ScopeLevel y = x >= y

instance JoinSemiLattice ScopeLevel where
    ScopeLevel x \/ ScopeLevel y = ScopeLevel (min x y)

instance BoundedJoinSemiLattice ScopeLevel where
    bottom = ScopeLevel maxBound

instance Pretty ScopeLevel where
    pPrint (ScopeLevel x) = Pretty.text "scope#" <> pPrint x

instance NFData ScopeLevel
instance Binary ScopeLevel
