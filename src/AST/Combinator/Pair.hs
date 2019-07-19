{-# LANGUAGE NoImplicitPrelude, DerivingStrategies, DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances, TypeFamilies, TemplateHaskell, ConstraintKinds #-}

module AST.Combinator.Pair
    ( Pair(..), pairFst, pairSnd
    ) where

import AST.Class.Applicative.TH (makeKApplicativeAndBases)
import AST.Class.Traversable.TH (makeKTraversableAndFoldable)
import AST.Knot (Tie, ChildrenTypesOf)
import Control.DeepSeq (NFData)
import Control.Lens (makeLenses)
import Data.Binary (Binary)
import Data.Constraint (Constraint)
import GHC.Generics (Generic)

import Prelude.Compat

data Pair a b k = MkPair
    { _pairFst :: Tie k a
    , _pairSnd :: Tie k b
    } deriving stock Generic

type instance ChildrenTypesOf (Pair a b) = Pair a b
makeLenses ''Pair
makeKApplicativeAndBases ''Pair
makeKTraversableAndFoldable ''Pair

type Deps a b k c = ((c (Tie k a), c (Tie k b)) :: Constraint)

deriving instance Deps a b k Eq   => Eq   (Pair a b k)
deriving instance Deps a b k Ord  => Ord  (Pair a b k)
deriving instance Deps a b k Show => Show (Pair a b k)
instance Deps a b k Binary => Binary (Pair a b k)
instance Deps a b k NFData => NFData (Pair a b k)
