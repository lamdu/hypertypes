{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TemplateHaskell, DeriveGeneric #-}

module AST.Combinator.Both
    ( Both(..), bothA, bothB
    ) where

import AST.Knot (Knot, NodeTypesOf)
import Control.DeepSeq (NFData)
import Control.Lens (makeLenses)
import Data.Binary (Binary)
import GHC.Generics (Generic)

import Prelude.Compat

data Both a b (k :: Knot) = Both
    { _bothA :: a k
    , _bothB :: b k
    } deriving (Eq, Ord, Show, Generic)
makeLenses ''Both

type instance NodeTypesOf (Both a b) = Both (NodeTypesOf a) (NodeTypesOf b)

instance (Binary (a k), Binary (b k)) => Binary (Both a b k)
instance (NFData (a k), NFData (b k)) => NFData (Both a b k)
