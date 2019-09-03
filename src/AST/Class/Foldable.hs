{-# LANGUAGE RankNTypes #-}

module AST.Class.Foldable
    ( KFoldable(..)
    , foldMapKWith, foldMapKWithWitness
    , foldMapK1
    , traverseK_, traverseKWith_, traverseK1_
    ) where

import AST.Class.Nodes (KNodes(..))
import AST.Knot (Knot, RunKnot, Tree)
import Control.Monad (join)
import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A variant of 'Foldable' for 'AST.Knot.Knot's
class KNodes k => KFoldable k where
    -- | 'KFoldable' variant of 'foldMap'
    foldMapK ::
        Monoid a =>
        (forall c. KWitness k c -> Tree l c -> a) ->
        Tree k l ->
        a

instance KFoldable (Const a) where
    {-# INLINE foldMapK #-}
    foldMapK _ _ = mempty

newtype FoldMapK a m (c :: Knot) = FoldMapK { getFoldMapK :: m c -> a }

-- | 'KFoldable' variant of 'foldMap' for functions with context
{-# INLINE foldMapKWith #-}
foldMapKWith ::
    (Monoid a, KFoldable k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child -> a) ->
    Tree k n ->
    a
foldMapKWith p f = foldMapK (getFoldMapK . kLiftConstraint p (FoldMapK f))

newtype FoldMapKW k a m c = FoldMapKW { getFoldMapKW :: KWitness k (RunKnot c) -> m c -> a }

{-# INLINE foldMapKWithWitness #-}
foldMapKWithWitness ::
    (Monoid a, KFoldable k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall child. constraint child => KWitness k child -> Tree n child -> a) ->
    Tree k n ->
    a
foldMapKWithWitness p f = foldMapK (join (getFoldMapKW . kLiftConstraint p (FoldMapKW f)))

-- TODO: Replace `foldMapK1` with `foldedK1` which is a `Fold`

-- | 'KFoldable' variant for 'foldMap' for 'AST.Knot.Knot's with a single node type (avoids using @RankNTypes@)
{-# INLINE foldMapK1 #-}
foldMapK1 ::
    forall a k c l.
    ( Monoid a, KFoldable k
    , NodesConstraint k ((~) c)
    ) =>
    (Tree l c -> a) ->
    Tree k l ->
    a
foldMapK1 = foldMapKWith (Proxy @((~) c))

-- | 'KFoldable' variant of 'Data.Foldable.traverse_'
{-# INLINE traverseK_ #-}
traverseK_ ::
    (Applicative f, KFoldable k) =>
    (forall c. Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK_ f = sequenceA_ . foldMapK (const ((:[]) . f))

-- | 'KFoldable' variant of 'Data.Foldable.traverse_' for functions with context
{-# INLINE traverseKWith_ #-}
traverseKWith_ ::
    forall f k constraint m.
    (Applicative f, KFoldable k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseKWith_ p f =
    sequenceA_ . foldMapKWith @[f ()] p ((:[]) . f)

-- | 'KFoldable' variant of 'Data.Foldable.traverse_' for 'AST.Knot.Knot's with a single node type (avoids using @RankNTypes@)
{-# INLINE traverseK1_ #-}
traverseK1_ ::
    forall f k c m.
    ( Applicative f, KFoldable k
    , NodesConstraint k ((~) c)
    ) =>
    (Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK1_ = traverseKWith_ (Proxy @((~) c))
