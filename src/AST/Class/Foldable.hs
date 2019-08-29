{-# LANGUAGE RankNTypes #-}

module AST.Class.Foldable
    ( KFoldable(..)
    , foldMapK1
    , traverseK_, traverseKWith_, traverseK1_
    ) where

import AST.Class.Nodes (KNodes(..))
import AST.Knot (Tree)
import Data.Constraint (withDict)
import Data.Constraint.List (NoConstraint)
import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A variant of 'Foldable' for 'AST.Knot.Knot's.
class KNodes k => KFoldable k where
    -- | 'KFoldable' variant of 'foldMap'
    foldMapK ::
        Monoid a =>
        (forall c. Tree l c -> a) ->
        Tree k l ->
        a
    {-# INLINE foldMapK #-}
    foldMapK f =
        withDict (kNoConstraints (Proxy @k)) $
        foldMapKWith (Proxy @NoConstraint) f

    -- | 'KFoldable' variant of 'foldMap' for functions with context
    foldMapKWith ::
        (Monoid a, NodesConstraint k constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child -> a) ->
        Tree k n ->
        a

instance KFoldable (Const a) where
    {-# INLINE foldMapKWith #-}
    foldMapKWith _ _ _ = mempty

-- TODO: Replace `foldMapK1` with `foldedK1` which is a `Fold`

-- | 'KFoldable' variant for 'foldMap' for 'AST.Knot.Knot's with a single node type (avoids using `RankNTypes`)
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
traverseK_ f = sequenceA_ . foldMapK ((:[]) . f)

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
    sequenceA_ . foldMapKWith @_ @[f ()] p ((:[]) . f)

-- | 'KFoldable' variant of 'Data.Foldable.traverse_' for 'AST.Knot.Knot's with a single node type (avoids using `RankNTypes`)
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
