{-# LANGUAGE TemplateHaskellQuotes #-}

module Hyper.Internal.Prelude
    ( makeCommonInstances

    , module X
    ) where

import Control.DeepSeq as X (NFData)
import Control.Lens as X (Traversal, Iso, makeLenses, makePrisms)
import Control.Lens.Operators as X
import Control.Monad as X (guard)
import Data.Binary as X (Binary)
import Data.Constraint as X (Dict(..), Constraint, withDict)
import Data.Foldable as X (traverse_, sequenceA_)
import Data.Functor.Const as X (Const(..))
import Data.Proxy as X (Proxy(..))
import Data.Map as X (Map)
import Data.Maybe as X (fromMaybe)
import Data.Set as X (Set)
import Generics.Constraints (makeDerivings, makeInstances)
import GHC.Generics as X (Generic, (:*:)(..))
import Language.Haskell.TH (Name, DecsQ)

import Prelude.Compat as X

-- Derive a specific list of classes that types in hypertypes implement.
makeCommonInstances :: [Name] -> DecsQ
makeCommonInstances names =
    (<>)
    <$> makeDerivings [''Eq, ''Ord, ''Show] names
    <*> makeInstances [''Binary, ''NFData] names
