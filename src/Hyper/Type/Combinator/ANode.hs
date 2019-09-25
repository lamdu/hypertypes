{-# LANGUAGE UndecidableInstances, TemplateHaskell, FlexibleInstances #-}

-- | A simple 'Hyper.Type.AHyperType' with a single child node

module Hyper.Type.Combinator.ANode
    ( ANode(..), _ANode
    ) where

import Hyper.Class.Has (HasChild(..))
import Hyper.Type (Tree, type (#))
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.TH.Traversable (makeKTraversableApplyAndBases)
import Control.Lens (Iso, iso)
import GHC.Generics (Generic)

-- | @ANode c@ is a 'Hyper.Type.AHyperType' with a single child node of type @c@
newtype ANode c k = MkANode (k # c)
    deriving stock Generic

-- | An 'Iso' from 'ANode' its child node.
--
-- Using `_ANode` rather than the 'MkANode' data constructor is recommended,
-- because it helps the type inference know that @ANode c@ is parameterized with a 'Hyper.Type.AHyperType'.
{-# INLINE _ANode #-}
_ANode :: Iso (Tree (ANode c0) k0) (Tree (ANode c1) k1) (Tree k0 c0) (Tree k1 c1)
_ANode = iso (\(MkANode x) -> x) MkANode

makeKTraversableApplyAndBases ''ANode
makeCommonInstances [''ANode]

instance HasChild (ANode c) c where
    {-# INLINE getChild #-}
    getChild = _ANode
