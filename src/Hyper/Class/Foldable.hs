-- | A variant of 'Foldable' for 'Hyper.Type.AHyperType's

module Hyper.Class.Foldable
    ( HFoldable(..)
    , foldMapH1
    , traverseH_, traverseH1_
    ) where

import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))
import Data.Proxy (Proxy(..))
import Hyper.Class.Nodes (HNodes(..), HWitness(..), (#>))
import Hyper.Type (Tree)

import Prelude.Compat

-- | A variant of 'Foldable' for 'Hyper.Type.AHyperType's
class HNodes h => HFoldable h where
    -- | 'HFoldable' variant of 'foldMap'
    --
    -- Gets a function from @h@'s nodes (trees along witnesses that they are nodes of @h@)
    -- into a monoid and concats its results for all nodes.
    foldMapH ::
        Monoid a =>
        (forall n. HWitness h n -> Tree p n -> a) ->
        Tree h p ->
        a

instance HFoldable (Const a) where
    {-# INLINE foldMapH #-}
    foldMapH _ _ = mempty

instance (HFoldable a, HFoldable b) => HFoldable (Product a b) where
    {-# INLINE foldMapH #-}
    foldMapH f (Pair x y) = foldMapH (f . E_Product_a) x <> foldMapH (f . E_Product_b) y

instance (HFoldable a, HFoldable b) => HFoldable (Sum a b) where
    {-# INLINE foldMapH #-}
    foldMapH f (InL x) = foldMapH (f . E_Sum_a) x
    foldMapH f (InR x) = foldMapH (f . E_Sum_b) x

-- TODO: Replace `foldMapH1` with `foldedK1` which is a `Fold`

-- | 'HFoldable' variant for 'foldMap' for 'Hyper.Type.AHyperType's with a single node type (avoids using @RankNTypes@)
{-# INLINE foldMapH1 #-}
foldMapH1 ::
    forall a h n p.
    ( Monoid a, HFoldable h
    , HNodesConstraint h ((~) n)
    ) =>
    (Tree p n -> a) ->
    Tree h p ->
    a
foldMapH1 f = foldMapH (Proxy @((~) n) #> f)

-- | 'HFoldable' variant of 'Data.Foldable.traverse_'
--
-- Applise a given action on all subtrees
-- (represented as trees along witnesses that they are nodes of @h@)
{-# INLINE traverseH_ #-}
traverseH_ ::
    (Applicative f, HFoldable h) =>
    (forall c. HWitness h c -> Tree m c -> f ()) ->
    Tree h m ->
    f ()
traverseH_ f = sequenceA_ . foldMapH (fmap (:[]) . f)

-- | 'HFoldable' variant of 'Data.Foldable.traverse_' for 'Hyper.Type.AHyperType's with a single node type (avoids using @RankNTypes@)
{-# INLINE traverseH1_ #-}
traverseH1_ ::
    forall f h n p.
    ( Applicative f, HFoldable h
    , HNodesConstraint h ((~) n)
    ) =>
    (Tree p n -> f ()) ->
    Tree h p ->
    f ()
traverseH1_ f = traverseH_ (Proxy @((~) n) #> f)
