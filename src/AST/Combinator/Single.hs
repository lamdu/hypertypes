{-# LANGUAGE NoImplicitPrelude, DerivingStrategies, DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances, TypeFamilies, TemplateHaskell #-}

module AST.Combinator.Single
    ( Single(..)
    ) where

import AST.Class.Functor.TH (makeKFunctor)
import AST.Class.Pointed.TH (makeKPointed)
import AST.Knot (Tree, Tie, ChildrenTypesOf)
import Control.DeepSeq (NFData)
import Control.Lens (Iso, iso)
import Data.Binary (Binary)
import GHC.Generics (Generic)

import Prelude.Compat

newtype Single c k = MkSingle { getSingle :: Tie k c }
    deriving stock Generic

{-# INLINE _Single #-}
_Single :: Iso (Tree (Single c0) k0) (Tree (Single c1) k1) (Tree k0 c0) (Tree k1 c1)
_Single = iso getSingle MkSingle

type instance ChildrenTypesOf (Single c) = Single c
makeKPointed ''Single
makeKFunctor ''Single

deriving instance Eq   (Tie k c) => Eq   (Single c k)
deriving instance Ord  (Tie k c) => Ord  (Single c k)
deriving instance Show (Tie k c) => Show (Single c k)
instance Binary (Tie k c) => Binary (Single c k)
instance NFData (Tie k c) => NFData (Single c k)
