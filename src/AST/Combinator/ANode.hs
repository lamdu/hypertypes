{-# LANGUAGE UndecidableInstances, TemplateHaskell #-}

module AST.Combinator.ANode
    ( ANode(..), _ANode
    ) where

import AST.Knot (Tree, Node)
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.TH.Traversable (makeKTraversableApplyAndBases)
import Control.Lens (Iso, iso)
import GHC.Generics (Generic)

newtype ANode c k = MkANode { getANode :: Node k c }
    deriving stock Generic

{-# INLINE _ANode #-}
_ANode :: Iso (Tree (ANode c0) k0) (Tree (ANode c1) k1) (Tree k0 c0) (Tree k1 c1)
_ANode = iso getANode MkANode

makeKTraversableApplyAndBases ''ANode
makeCommonInstances [''ANode]
