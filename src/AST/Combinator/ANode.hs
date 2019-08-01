{-# LANGUAGE NoImplicitPrelude, DerivingStrategies, DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances, TypeFamilies, TemplateHaskell, DataKinds #-}

module AST.Combinator.ANode
    ( ANode(..), _ANode
    ) where

import AST.Class (KNodes(..))
import AST.Class.Apply.TH (makeKApplicativeBases)
import AST.Knot (Tree, Node)
import Control.DeepSeq (NFData)
import Control.Lens (Iso, iso)
import Data.Binary (Binary)
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

makeKApplicativeBases ''ANode

deriving instance Eq   (Node k c) => Eq   (ANode c k)
deriving instance Ord  (Node k c) => Ord  (ANode c k)
deriving instance Show (Node k c) => Show (ANode c k)
instance Binary (Node k c) => Binary (ANode c k)
instance NFData (Node k c) => NFData (ANode c k)
