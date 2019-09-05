{-# LANGUAGE RankNTypes #-}

module AST.Class.Foldable
    ( KFoldable(..)
    , foldMapK1
    , traverseK_, traverseK1_
    ) where

import AST.Class.Nodes (KNodes(..), (#>))
import AST.Knot (Tree)
import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A variant of 'Foldable' for 'AST.Knot.Knot's
class KNodes k => KFoldable k where
    -- | 'KFoldable' variant of 'foldMap'
    --
    -- Gets a function from @k@'s nodes (trees along witnesses that they are nodes of @k@)
    -- into a monoid and concats its results for all nodes.
    foldMapK ::
        Monoid a =>
        (forall n. KWitness k n -> Tree p n -> a) ->
        Tree k p ->
        a

instance KFoldable (Const a) where
    {-# INLINE foldMapK #-}
    foldMapK _ _ = mempty

-- TODO: Replace `foldMapK1` with `foldedK1` which is a `Fold`

-- | 'KFoldable' variant for 'foldMap' for 'AST.Knot.Knot's with a single node type (avoids using @RankNTypes@)
{-# INLINE foldMapK1 #-}
foldMapK1 ::
    forall a k n p.
    ( Monoid a, KFoldable k
    , KNodesConstraint k ((~) n)
    ) =>
    (Tree p n -> a) ->
    Tree k p ->
    a
foldMapK1 f = foldMapK (Proxy @((~) n) #> f)

-- | 'KFoldable' variant of 'Data.Foldable.traverse_'
--
-- Applise a given action on all subtrees
-- (represented as trees along witnesses that they are nodes of @k@)
{-# INLINE traverseK_ #-}
traverseK_ ::
    (Applicative f, KFoldable k) =>
    (forall c. KWitness k c -> Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK_ f = sequenceA_ . foldMapK (fmap (:[]) . f)

-- | 'KFoldable' variant of 'Data.Foldable.traverse_' for 'AST.Knot.Knot's with a single node type (avoids using @RankNTypes@)
{-# INLINE traverseK1_ #-}
traverseK1_ ::
    forall f k n p.
    ( Applicative f, KFoldable k
    , KNodesConstraint k ((~) n)
    ) =>
    (Tree p n -> f ()) ->
    Tree k p ->
    f ()
traverseK1_ f = traverseK_ (Proxy @((~) n) #> f)
