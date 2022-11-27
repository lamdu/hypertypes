{-# LANGUAGE TemplateHaskellQuotes #-}

module Hyper.Internal.Prelude
    ( makeCommonInstances
    , module X
    ) where

import Control.DeepSeq as X (NFData)
import Control.Lens as X (Iso, Traversal, makeLenses, makePrisms)
import Control.Lens.Operators as X
import Control.Monad as X (guard, void)
import Data.Binary as X (Binary)
import Data.Constraint as X (Constraint, Dict (..), (\\))
import Data.Foldable as X (sequenceA_, traverse_)
import Data.Functor.Const as X (Const (..))
import Data.Map as X (Map)
import Data.Maybe as X (fromMaybe)
import Data.Proxy as X (Proxy (..))
import Data.Set as X (Set)
import GHC.Generics as X (Generic, (:*:) (..))
import Generics.Constraints (makeDerivings, makeInstances)
import Language.Haskell.TH (DecsQ, Name)

import Prelude.Compat as X

-- Derive a specific list of classes that types in hypertypes implement.
makeCommonInstances :: [Name] -> DecsQ
makeCommonInstances names =
    (<>)
        <$> makeDerivings [''Eq, ''Ord, ''Show] names
        <*> makeInstances [''Binary, ''NFData] names
