{-# LANGUAGE RankNTypes #-}

module AST.Class.Traversable
    ( KTraversable(..)
    , ContainedK(..), _ContainedK
    , traverseK, traverseKWith, traverseK1
    ) where

import AST.Class.Foldable (KFoldable)
import AST.Class.Functor (KFunctor(..), mapKWith, mappedK1)
import AST.Class.Nodes (KNodes(..))
import AST.Knot (Knot, Tree)
import Control.Lens (Traversal, Iso, iso)
import Control.Lens.Operators
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A 'Knot' containing a tree inside an action.
--
-- Used to express 'sequenceK'.
newtype ContainedK f p (k :: Knot) = MkContainedK { runContainedK :: f (p k) }

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

-- | 'KTraversable' variant of 'traverse'
{-# INLINE traverseK #-}
traverseK ::
    (Applicative f, KTraversable k) =>
    (forall n. KWitness k n -> Tree p n -> f (Tree q n)) ->
    Tree k p ->
    f (Tree k q)
traverseK f = sequenceK . mapK (fmap MkContainedK . f)

-- | Variant of 'traverseK' for functions with context instead of a witness parameter
{-# INLINE traverseKWith #-}
traverseKWith ::
    (Applicative f, KTraversable k, KNodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseKWith p f = sequenceK . mapKWith p (MkContainedK . f)

-- | 'KTraversable' variant of 'traverse' for 'Knot's with a single node type.
--
-- It is a valid 'Traversal' as it avoids using @RankNTypes@.
{-# INLINE traverseK1 #-}
traverseK1 ::
    (KTraversable k, KNodesConstraint k ((~) n)) =>
    Traversal (Tree k p) (Tree k q) (Tree p n) (Tree q n)
traverseK1 f = sequenceK . (mappedK1 %~ (MkContainedK . f))
