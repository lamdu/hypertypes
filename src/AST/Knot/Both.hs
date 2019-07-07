{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TemplateHaskell #-}

module AST.Knot.Both
    ( Both(..), bothA, bothB
    ) where

import AST.Class.Children.TH (makeChildren)
import AST.Knot (Knot)
import Control.Lens (makeLenses)

import Prelude.Compat

data Both a b (k :: Knot) = Both
    { _bothA :: a k
    , _bothB :: b k
    } deriving (Eq, Ord, Show)
makeLenses ''Both

makeChildren ''Both
