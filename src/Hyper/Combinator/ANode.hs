{-# LANGUAGE UndecidableInstances, TemplateHaskell, FlexibleInstances #-}

-- | A simple 'Hyper.Type.HyperType' with a single child node

module Hyper.Combinator.ANode
    ( ANode(..), _ANode, W_ANode(..)
    ) where

import Control.Lens (Iso, iso)
import GHC.Generics (Generic)
import Hyper.Class.Has (HasChild(..))
import Hyper.Class.Recursive (RNodes, Recursively, RTraversable)
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (type (#), type (:#))

-- | @ANode c@ is a 'Hyper.Type.HyperType' with a single child node of type @c@
newtype ANode c h = MkANode (h :# c)
    deriving stock Generic

-- | An 'Iso' from 'ANode' its child node.
--
-- Using `_ANode` rather than the 'MkANode' data constructor is recommended,
-- because it helps the type inference know that @ANode c@ is parameterized with a 'Hyper.Type.HyperType'.
{-# INLINE _ANode #-}
_ANode :: Iso (ANode c0 # k0) (ANode c1 # k1) (k0 # c0) (k1 # c1)
_ANode = iso (\(MkANode x) -> x) MkANode

makeHTraversableApplyAndBases ''ANode
makeCommonInstances [''ANode]

instance HasChild (ANode c) c where
    {-# INLINE getChild #-}
    getChild = _ANode

instance RNodes n => RNodes (ANode n)
instance (c (ANode n), Recursively c n) => Recursively c (ANode n)
instance RTraversable n => RTraversable (ANode n)
