{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TemplateHaskell, DeriveGeneric #-}

module AST.Combinator.Both
    ( Both(..), bothA, bothB
    ) where

import AST.Class.Functor.TH (makeKFunctor)
import AST.Class.Pointed.TH (makeKPointed)
import AST.Class.Traversable.TH (makeKTraversableAndFoldable)
import AST.Knot (Knot, ChildrenTypesOf)
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

type instance ChildrenTypesOf (Both a b) = Both (ChildrenTypesOf a) (ChildrenTypesOf b)

-- KApply instance declared in AST.Class.Apply
makeKFunctor ''Both
makeKPointed ''Both
makeKTraversableAndFoldable ''Both

instance (Binary (a k), Binary (b k)) => Binary (Both a b k)
instance (NFData (a k), NFData (b k)) => NFData (Both a b k)
