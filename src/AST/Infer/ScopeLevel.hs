{-# LANGUAGE TemplateHaskell #-}

module AST.Infer.ScopeLevel
    ( MonadScopeLevel(..)
    , ScopeLevel(..), _ScopeLevel
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import           AST.Unify.Constraints (TypeConstraints(..))
import           Control.DeepSeq (NFData)
import           Data.Binary (Binary)
import           Control.Lens (makePrisms)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

class Monad m => MonadScopeLevel m where
    localLevel :: m a -> m a

-- | NOTE: The `Ord` instance is only for use as a `Map` key, not a
-- logical ordering
newtype ScopeLevel = ScopeLevel Int
    deriving stock (Eq, Ord, Show, Generic)
makePrisms ''ScopeLevel

instance PartialOrd ScopeLevel where
    ScopeLevel x `leq` ScopeLevel y = x >= y

instance Semigroup ScopeLevel where
    ScopeLevel x <> ScopeLevel y = ScopeLevel (min x y)

instance Monoid ScopeLevel where
    mempty = ScopeLevel maxBound

instance TypeConstraints ScopeLevel where
    generalizeConstraints _ = mempty
    toScopeConstraints = id

instance Pretty ScopeLevel where
    pPrint (ScopeLevel x) = Pretty.text "scope#" <> pPrint x

instance NFData ScopeLevel
instance Binary ScopeLevel
