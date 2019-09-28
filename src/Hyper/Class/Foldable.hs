-- | A variant of 'Foldable' for 'Hyper.Type.HyperType's

module Hyper.Class.Foldable
    ( HFoldable(..)
    , hfolded1
    , htraverse_, htraverse1_
    ) where

import Control.Lens (Fold, folding)
import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))
import GHC.Generics ((:*:)(..), (:+:)(..))
import Hyper.Class.Nodes (HNodes(..), HWitness(..), (#>))
import Hyper.Type (Tree)

import Prelude.Compat

-- | A variant of 'Foldable' for 'Hyper.Type.HyperType's
class HNodes h => HFoldable h where
    -- | 'HFoldable' variant of 'foldMap'
    --
    -- Gets a function from @h@'s nodes (trees along witnesses that they are nodes of @h@)
    -- into a monoid and concats its results for all nodes.
    hfoldMap ::
        Monoid a =>
        (forall n. HWitness h n -> Tree p n -> a) ->
        Tree h p ->
        a

instance HFoldable (Const a) where
    {-# INLINE hfoldMap #-}
    hfoldMap _ _ = mempty

instance (HFoldable a, HFoldable b) => HFoldable (a :*: b) where
    {-# INLINE hfoldMap #-}
    hfoldMap f (x :*: y) = hfoldMap (f . E_Product_a) x <> hfoldMap (f . E_Product_b) y

instance (HFoldable a, HFoldable b) => HFoldable (a :+: b) where
    {-# INLINE hfoldMap #-}
    hfoldMap f (L1 x) = hfoldMap (f . E_Sum_a) x
    hfoldMap f (R1 x) = hfoldMap (f . E_Sum_b) x

-- | 'HFoldable' variant for 'Control.Lens.folded' for 'Hyper.Type.HyperType's with a single node type.
--
-- Avoids using @RankNTypes@ and thus can be composed with other optics.
{-# INLINE hfolded1 #-}
hfolded1 ::
    forall h n p.
    ( HFoldable h
    , HNodesConstraint h ((~) n)
    ) =>
    Fold (Tree h p) (Tree p n)
hfolded1 =
    folding (hfoldMap @_ @[Tree p n] (Proxy @((~) n) #> pure))

-- | 'HFoldable' variant of 'Data.Foldable.traverse_'
--
-- Applise a given action on all subtrees
-- (represented as trees along witnesses that they are nodes of @h@)
{-# INLINE htraverse_ #-}
htraverse_ ::
    (Applicative f, HFoldable h) =>
    (forall c. HWitness h c -> Tree m c -> f ()) ->
    Tree h m ->
    f ()
htraverse_ f = sequenceA_ . hfoldMap (fmap (:[]) . f)

-- | 'HFoldable' variant of 'Data.Foldable.traverse_' for 'Hyper.Type.HyperType's with a single node type (avoids using @RankNTypes@)
{-# INLINE htraverse1_ #-}
htraverse1_ ::
    forall f h n p.
    ( Applicative f, HFoldable h
    , HNodesConstraint h ((~) n)
    ) =>
    (Tree p n -> f ()) ->
    Tree h p ->
    f ()
htraverse1_ f = htraverse_ (Proxy @((~) n) #> f)
