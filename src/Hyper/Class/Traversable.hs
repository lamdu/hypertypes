-- | A variant of 'Traversable' for 'AHyperType's

module Hyper.Class.Traversable
    ( HTraversable(..)
    , ContainedK(..), _ContainedK
    , traverseK, traverseK1
    ) where

import Control.Lens (Traversal, Iso, iso)
import Control.Lens.Operators
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))
import Hyper.Class.Foldable (HFoldable)
import Hyper.Class.Functor (HFunctor(..), mappedK1)
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Type (AHyperType, Tree)

import Prelude.Compat

-- | A 'AHyperType' containing a tree inside an action.
--
-- Used to express 'sequenceK'.
newtype ContainedK f p (h :: AHyperType) = MkContainedK { runContainedK :: f (p h) }

-- | An 'Iso' for the 'ContainedK' @newtype@
{-# INLINE _ContainedK #-}
_ContainedK ::
    Iso (Tree (ContainedK f0 p0) k0)
        (Tree (ContainedK f1 p1) k1)
        (f0 (Tree p0 k0))
        (f1 (Tree p1 k1))
_ContainedK = iso runContainedK MkContainedK

-- | A variant of 'Traversable' for 'AHyperType's
class (HFunctor h, HFoldable h) => HTraversable h where
    -- | 'HTraversable' variant of 'sequenceA'
    sequenceK ::
        Applicative f =>
        Tree h (ContainedK f p) ->
        f (Tree h p)

instance HTraversable (Const a) where
    {-# INLINE sequenceK #-}
    sequenceK (Const x) = pure (Const x)

instance (HTraversable a, HTraversable b) => HTraversable (Product a b) where
    {-# INLINE sequenceK #-}
    sequenceK (Pair x y) = Pair <$> sequenceK x <*> sequenceK y

instance (HTraversable a, HTraversable b) => HTraversable (Sum a b) where
    {-# INLINE sequenceK #-}
    sequenceK (InL x) = sequenceK x <&> InL
    sequenceK (InR x) = sequenceK x <&> InR

-- | 'HTraversable' variant of 'traverse'
{-# INLINE traverseK #-}
traverseK ::
    (Applicative f, HTraversable h) =>
    (forall n. HWitness h n -> Tree p n -> f (Tree q n)) ->
    Tree h p ->
    f (Tree h q)
traverseK f = sequenceK . mapK (fmap MkContainedK . f)

-- | 'HTraversable' variant of 'traverse' for 'AHyperType's with a single node type.
--
-- It is a valid 'Traversal' as it avoids using @RankNTypes@.
{-# INLINE traverseK1 #-}
traverseK1 ::
    (HTraversable h, HNodesConstraint h ((~) n)) =>
    Traversal (Tree h p) (Tree h q) (Tree p n) (Tree q n)
traverseK1 f = sequenceK . (mappedK1 %~ (MkContainedK . f))
