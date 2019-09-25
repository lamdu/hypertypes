-- | A variant of 'Traversable' for 'Hyper.Type.HyperType's

module Hyper.Class.Traversable
    ( HTraversable(..)
    , ContainedH(..), _ContainedH
    , traverseH, traverseH1
    ) where

import Control.Lens (Traversal, Iso, iso)
import Control.Lens.Operators
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))
import Hyper.Class.Foldable (HFoldable)
import Hyper.Class.Functor (HFunctor(..), mappedH1)
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Type (AHyperType, Tree)

import Prelude.Compat

-- | A 'Hyper.Type.HyperType' containing a tree inside an action.
--
-- Used to express 'sequenceH'.
newtype ContainedH f p (h :: AHyperType) = MkContainedH { runContainedH :: f (p h) }

-- | An 'Iso' for the 'ContainedH' @newtype@
{-# INLINE _ContainedH #-}
_ContainedH ::
    Iso (Tree (ContainedH f0 p0) k0)
        (Tree (ContainedH f1 p1) k1)
        (f0 (Tree p0 k0))
        (f1 (Tree p1 k1))
_ContainedH = iso runContainedH MkContainedH

-- | A variant of 'Traversable' for 'Hyper.Type.HyperType's
class (HFunctor h, HFoldable h) => HTraversable h where
    -- | 'HTraversable' variant of 'sequenceA'
    sequenceH ::
        Applicative f =>
        Tree h (ContainedH f p) ->
        f (Tree h p)

instance HTraversable (Const a) where
    {-# INLINE sequenceH #-}
    sequenceH (Const x) = pure (Const x)

instance (HTraversable a, HTraversable b) => HTraversable (Product a b) where
    {-# INLINE sequenceH #-}
    sequenceH (Pair x y) = Pair <$> sequenceH x <*> sequenceH y

instance (HTraversable a, HTraversable b) => HTraversable (Sum a b) where
    {-# INLINE sequenceH #-}
    sequenceH (InL x) = sequenceH x <&> InL
    sequenceH (InR x) = sequenceH x <&> InR

-- | 'HTraversable' variant of 'traverse'
{-# INLINE traverseH #-}
traverseH ::
    (Applicative f, HTraversable h) =>
    (forall n. HWitness h n -> Tree p n -> f (Tree q n)) ->
    Tree h p ->
    f (Tree h q)
traverseH f = sequenceH . mapH (fmap MkContainedH . f)

-- | 'HTraversable' variant of 'traverse' for 'Hyper.Type.HyperType's with a single node type.
--
-- It is a valid 'Traversal' as it avoids using @RankNTypes@.
{-# INLINE traverseH1 #-}
traverseH1 ::
    (HTraversable h, HNodesConstraint h ((~) n)) =>
    Traversal (Tree h p) (Tree h q) (Tree p n) (Tree q n)
traverseH1 f = sequenceH . (mappedH1 %~ (MkContainedH . f))
