{-# LANGUAGE UndecidableInstances, TemplateHaskell, GADTs, FlexibleInstances #-}

module AST.Combinator.ANode
    ( ANode(..), _ANode
    ) where

import AST.Knot (Tree, Node)
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.TH.Traversable (makeKTraversableApplyAndBases)
import Control.Lens (Iso, iso)
import GHC.Generics (Generic)

-- | @ANode c@ is a 'AST.Knot.Knot' with a single child node of type @c@
newtype ANode c k = MkANode (Node k c)
    deriving stock Generic

-- | An 'Iso' from 'ANode' its child node.
--
-- Using `_ANode` rather than the 'MkANode' data constructor is recommended,
-- because it helps the type inference know that @ANode c@ is parameterized with a 'AST.Knot.Knot'.
{-# INLINE _ANode #-}
_ANode :: Iso (Tree (ANode c0) k0) (Tree (ANode c1) k1) (Tree k0 c0) (Tree k1 c1)
_ANode = iso (\(MkANode x) -> x) MkANode

makeKTraversableApplyAndBases ''ANode
makeCommonInstances [''ANode]
