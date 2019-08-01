{-# LANGUAGE NoImplicitPrelude, DerivingStrategies, DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances, TypeFamilies, TemplateHaskell, DataKinds #-}

module AST.Combinator.ANode
    ( ANode(..), _ANode
    ) where

import AST.Class
import AST.Knot (Tree, Node)
import AST.TH.Pointed (makeKPointed)
import Control.DeepSeq (NFData)
import Control.Lens (Iso, iso)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Functor.Product.PolyKinds
import Data.TyFun (On)
import GHC.Generics (Generic)

import Prelude.Compat

newtype ANode c k = MkANode { getANode :: Node k c }
    deriving stock Generic

{-# INLINE _ANode #-}
_ANode :: Iso (Tree (ANode c0) k0) (Tree (ANode c1) k1) (Tree k0 c0) (Tree k1 c1)
_ANode = iso getANode MkANode

instance KNodes (ANode c) where
    type NodeTypesOf (ANode c) = ANode c
    type NodesConstraint (ANode c) = On c

makeKPointed ''ANode
instance KFunctor (ANode c) where mapC = (_ANode %~) . (^. _ANode . _MapK)
instance KApply (ANode c) where zipK = (_ANode %~) . (Pair . getANode)

deriving instance Eq   (Node k c) => Eq   (ANode c k)
deriving instance Ord  (Node k c) => Ord  (ANode c k)
deriving instance Show (Node k c) => Show (ANode c k)
instance Binary (Node k c) => Binary (ANode c k)
instance NFData (Node k c) => NFData (ANode c k)
