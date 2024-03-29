{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A simple 'Hyper.Type.HyperType' with a single child node
module Hyper.Combinator.ANode
    ( ANode (..)
    , _ANode
    , W_ANode (..)
    , MorphWitness (..)
    ) where

import Control.Lens (iso)
import Hyper.Class.Morph (HMorph (..))
import Hyper.Class.Optic (HNodeLens (..))
import Hyper.Class.Recursive (RNodes, RTraversable, Recursively)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (type (#), type (:#))

import Hyper.Internal.Prelude

-- | @ANode c@ is a 'Hyper.Type.HyperType' with a single child node of type @c@
newtype ANode c h = MkANode (h :# c)
    deriving stock (Generic)

-- | An 'Iso' from 'ANode' its child node.
--
-- Using `_ANode` rather than the 'MkANode' data constructor is recommended,
-- because it helps the type inference know that @ANode c@ is parameterized with a 'Hyper.Type.HyperType'.
{-# INLINE _ANode #-}
_ANode :: Iso (ANode c0 # k0) (ANode c1 # k1) (k0 # c0) (k1 # c1)
_ANode = iso (\(MkANode x) -> x) MkANode

makeHTraversableApplyAndBases ''ANode
makeCommonInstances [''ANode]

instance HNodeLens (ANode c) c where hNodeLens = _ANode

instance RNodes n => RNodes (ANode n)
instance (c (ANode n), Recursively c n) => Recursively c (ANode n)
instance RTraversable n => RTraversable (ANode n)

instance HMorph (ANode a) (ANode b) where
    type MorphConstraint (ANode a) (ANode b) c = c a b
    data MorphWitness (ANode a) (ANode b) _ _ where
        M_ANode :: MorphWitness (ANode a) (ANode b) a b
    morphMap f = _ANode %~ f M_ANode
    morphLiftConstraint M_ANode _ x = x
