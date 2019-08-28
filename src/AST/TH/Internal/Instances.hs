{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Internal.Instances
    ( makeCommonInstances
    ) where

import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Language.Haskell.TH (Name, DecsQ)
import Generics.Constraints (makeDerivings, makeInstances)

import Prelude.Compat

-- Derive a specific list of classes that types in syntax-tree implement.
makeCommonInstances :: [Name] -> DecsQ
makeCommonInstances names =
    (<>)
    <$> makeDerivings [''Eq, ''Ord, ''Show] names
    <*> makeInstances [''Binary, ''NFData] names
