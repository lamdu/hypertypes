-- | A variant of 'Traversable' for 'Hyper.Type.HyperType's

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.Traversable
    ( HTraversable(..)
    , ContainedH(..), _ContainedH
    , htraverse, htraverse1
    ) where

import Control.Lens (iso)
import GHC.Generics
import GHC.Generics.Lens (_M1, _Rec1, generic1)
import Hyper.Class.Foldable (HFoldable)
import Hyper.Class.Functor (HFunctor(..), hmapped1)
import Hyper.Class.Nodes (HNodes(..), HWitness)
import Hyper.Type (AHyperType, type (#))

import Hyper.Internal.Prelude

-- | A 'Hyper.Type.HyperType' containing a tree inside an action.
--
-- Used to express 'hsequence'.
newtype ContainedH f p (h :: AHyperType) = MkContainedH { runContainedH :: f (p h) }

-- | An 'Iso' for the 'ContainedH' @newtype@
{-# INLINE _ContainedH #-}
_ContainedH ::
    Iso (ContainedH f0 p0 # k0)
        (ContainedH f1 p1 # k1)
        (f0 (p0 # k0))
        (f1 (p1 # k1))
_ContainedH = iso runContainedH MkContainedH

-- | A variant of 'Traversable' for 'Hyper.Type.HyperType's
class (HFunctor h, HFoldable h) => HTraversable h where
    -- | 'HTraversable' variant of 'sequenceA'
    hsequence ::
        Applicative f =>
        h # ContainedH f p ->
        f (h # p)
    {-# INLINE hsequence #-}
    default hsequence ::
        (Generic1 h, HTraversable (Rep1 h), Applicative f) =>
        h # ContainedH f p ->
        f (h # p)
    hsequence = generic1 hsequence

instance HTraversable (Const a) where
    {-# INLINE hsequence #-}
    hsequence (Const x) = pure (Const x)

instance (HTraversable a, HTraversable b) => HTraversable (a :*: b) where
    {-# INLINE hsequence #-}
    hsequence (x :*: y) = (:*:) <$> hsequence x <*> hsequence y

instance (HTraversable a, HTraversable b) => HTraversable (a :+: b) where
    {-# INLINE hsequence #-}
    hsequence (L1 x) = hsequence x <&> L1
    hsequence (R1 x) = hsequence x <&> R1

instance HTraversable h => HTraversable (M1 i m h) where
    {-# INLINE hsequence #-}
    hsequence = _M1 hsequence

instance HTraversable h => HTraversable (Rec1 h) where
    {-# INLINE hsequence #-}
    hsequence = _Rec1 hsequence

-- | 'HTraversable' variant of 'traverse'
{-# INLINE htraverse #-}
htraverse ::
    (Applicative f, HTraversable h) =>
    (forall n. HWitness h n -> p # n -> f (q # n)) ->
    h # p ->
    f (h # q)
htraverse f = hsequence . hmap (fmap MkContainedH . f)

-- | 'HTraversable' variant of 'traverse' for 'Hyper.Type.HyperType's with a single node type.
--
-- It is a valid 'Traversal' as it avoids using @RankNTypes@.
{-# INLINE htraverse1 #-}
htraverse1 ::
    (HTraversable h, HNodesConstraint h ((~) n)) =>
    Traversal (h # p) (h # q) (p # n) (q # n)
htraverse1 f = hsequence . (hmapped1 %~ MkContainedH . f)
