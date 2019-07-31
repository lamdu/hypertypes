{-# LANGUAGE NoImplicitPrelude, DerivingStrategies, DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances, TypeFamilies, TemplateHaskell, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, DataKinds #-}

module AST.Combinator.Pair
    ( Pair(..), pairFst, pairSnd
    ) where

import AST.Class (KNodes(..))
import AST.Class.Apply.TH (makeKApplicativeBases)
import AST.Class.Traversable.TH (makeKTraversableAndFoldable)
import AST.Class.Has (KHas(..))
import AST.Constraint
import AST.Combinator.Single (Single(..))
import AST.Knot (Node)
import Control.DeepSeq (NFData)
import Control.Lens (makeLenses)
import Data.Binary (Binary)
import Data.Constraint (Constraint)
import GHC.Generics (Generic)

import Prelude.Compat

data Pair a b k = MkPair
    { _pairFst :: Node k a
    , _pairSnd :: Node k b
    } deriving stock Generic

instance KNodes (Pair a b) where
    type NodeTypesOf (Pair a b) = Pair a b
    type NodesConstraint (Pair a b) = KnotsConstraint '[a, b]

makeLenses ''Pair
makeKApplicativeBases ''Pair
makeKTraversableAndFoldable ''Pair

-- Useful instance for when a type has a single child type,
-- but uses a parameterized AST term which may have two different types.
instance KHas (Pair a a) (Single a) where
    hasK (MkSingle x) = MkPair x x

instance KHas (Single a) (Pair a b) where
    hasK (MkPair x _) = MkSingle x

instance KHas (Single b) (Pair a b) where
    hasK (MkPair _ x) = MkSingle x

type Deps a b k c = ((c (Node k a), c (Node k b)) :: Constraint)

deriving instance Deps a b k Eq   => Eq   (Pair a b k)
deriving instance Deps a b k Ord  => Ord  (Pair a b k)
deriving instance Deps a b k Show => Show (Pair a b k)
instance Deps a b k Binary => Binary (Pair a b k)
instance Deps a b k NFData => NFData (Pair a b k)
