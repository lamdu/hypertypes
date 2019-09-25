{-# LANGUAGE TemplateHaskellQuotes #-}

module Hyper.TH.Internal.Instances
    ( makeCommonInstances
    ) where

import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Generics.Constraints (makeDerivings, makeInstances)
import Language.Haskell.TH (Name, DecsQ)

import Prelude.Compat

-- Derive a specific list of classes that types in hypertypes implement.
makeCommonInstances :: [Name] -> DecsQ
makeCommonInstances names =
    (<>)
    <$> makeDerivings [''Eq, ''Ord, ''Show] names
    <*> makeInstances [''Binary, ''NFData] names
