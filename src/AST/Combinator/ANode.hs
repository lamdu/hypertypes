{-# LANGUAGE UndecidableInstances, TemplateHaskell #-}

module AST.Combinator.ANode
    ( ANode(..), _ANode
    ) where

import AST.Class
import AST.Knot (Tree, Node)
import AST.TH.Apply (makeKApplicativeBases)
import AST.TH.Traversable (makeKTraversableAndFoldable)
import Control.DeepSeq (NFData)
import Control.Lens (Iso, iso)
import Data.Binary (Binary)
import Data.Constraint (Dict(..))
import GHC.Generics (Generic)

import Prelude.Compat

newtype ANode c k = MkANode { getANode :: Node k c }
    deriving stock Generic

{-# INLINE _ANode #-}
_ANode :: Iso (Tree (ANode c0) k0) (Tree (ANode c1) k1) (Tree k0 c0) (Tree k1 c1)
_ANode = iso getANode MkANode

instance KNodes (ANode k) where
    type instance NodesConstraint (ANode k) c = c k
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = Dict

makeKApplicativeBases ''ANode
makeKTraversableAndFoldable ''ANode

deriving instance Eq   (Node k c) => Eq   (ANode c k)
deriving instance Ord  (Node k c) => Ord  (ANode c k)
deriving instance Show (Node k c) => Show (ANode c k)
instance Binary (Node k c) => Binary (ANode c k)
instance NFData (Node k c) => NFData (ANode c k)
