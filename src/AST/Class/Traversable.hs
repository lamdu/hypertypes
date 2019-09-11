-- | A variant of 'Traversable' for 'Knot's

module AST.Class.Traversable
    ( KTraversable(..)
    , ContainedK(..), _ContainedK
    , traverseK, traverseK1
    ) where

import AST.Class.Foldable (KFoldable)
import AST.Class.Functor (KFunctor(..), mappedK1)
import AST.Class.Nodes (KNodes(..))
import AST.Knot (Knot, Tree)
import Control.Lens (Traversal, Iso, iso)
import Control.Lens.Operators
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))

import Prelude.Compat

-- | A 'Knot' containing a tree inside an action.
--
-- Used to express 'sequenceK'.
newtype ContainedK f p (k :: Knot) = MkContainedK { runContainedK :: f (p k) }

-- | An 'Iso' for the 'ContainedK' @newtype@
{-# INLINE _ContainedK #-}
_ContainedK ::
    Iso (Tree (ContainedK f0 p0) k0)
        (Tree (ContainedK f1 p1) k1)
        (f0 (Tree p0 k0))
        (f1 (Tree p1 k1))
_ContainedK = iso runContainedK MkContainedK

-- | A variant of 'Traversable' for 'Knot's
class (KFunctor k, KFoldable k) => KTraversable k where
    -- | 'KTraversable' variant of 'sequenceA'
    sequenceK ::
        Applicative f =>
        Tree k (ContainedK f p) ->
        f (Tree k p)

instance KTraversable (Const a) where
    {-# INLINE sequenceK #-}
    sequenceK (Const x) = pure (Const x)

instance (KTraversable a, KTraversable b) => KTraversable (Product a b) where
    {-# INLINE sequenceK #-}
    sequenceK (Pair x y) = Pair <$> sequenceK x <*> sequenceK y

instance (KTraversable a, KTraversable b) => KTraversable (Sum a b) where
    {-# INLINE sequenceK #-}
    sequenceK (InL x) = sequenceK x <&> InL
    sequenceK (InR x) = sequenceK x <&> InR

-- | 'KTraversable' variant of 'traverse'
{-# INLINE traverseK #-}
traverseK ::
    (Applicative f, KTraversable k) =>
    (forall n. KWitness k n -> Tree p n -> f (Tree q n)) ->
    Tree k p ->
    f (Tree k q)
traverseK f = sequenceK . mapK (fmap MkContainedK . f)

-- | 'KTraversable' variant of 'traverse' for 'Knot's with a single node type.
--
-- It is a valid 'Traversal' as it avoids using @RankNTypes@.
{-# INLINE traverseK1 #-}
traverseK1 ::
    (KTraversable k, KNodesConstraint k ((~) n)) =>
    Traversal (Tree k p) (Tree k q) (Tree p n) (Tree q n)
traverseK1 f = sequenceK . (mappedK1 %~ (MkContainedK . f))
