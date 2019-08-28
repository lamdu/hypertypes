{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Internal.Instances
    ( makeCommonInstances
    ) where

import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Control.Lens.Operators
import Language.Haskell.TH (Name, DecsQ)
import Generics.Constraints.TH (makeDeriving, makeInstance)

import Prelude.Compat

-- Derive a specific list of classes that types in syntax-tree implement.
makeCommonInstances :: Name -> DecsQ
makeCommonInstances name =
    (([''Eq, ''Ord, ''Show] <&> makeDeriving) <> ([''Binary, ''NFData] <&> makeInstance))
    ?? name
    & sequence <&> mconcat
