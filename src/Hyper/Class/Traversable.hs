-- | A variant of 'Traversable' for 'Hyper.Type.HyperType's

module Hyper.Class.Traversable
    ( HTraversable(..)
    , ContainedH(..), _ContainedH
    , htraverse, htraverse1
    ) where

import Control.Lens (Traversal, Iso, iso)
import Control.Lens.Operators
import Data.Functor.Const (Const(..))
import GHC.Generics ((:*:)(..), (:+:)(..))
import Hyper.Class.Foldable (HFoldable)
import Hyper.Class.Functor (HFunctor(..), hmapped1)
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Type (AHyperType, Tree)

import Prelude.Compat

-- | A 'Hyper.Type.HyperType' containing a tree inside an action.
--
-- Used to express 'hsequence'.
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
    hsequence ::
        Applicative f =>
        Tree h (ContainedH f p) ->
        f (Tree h p)

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

-- | 'HTraversable' variant of 'traverse'
{-# INLINE htraverse #-}
htraverse ::
    (Applicative f, HTraversable h) =>
    (forall n. HWitness h n -> Tree p n -> f (Tree q n)) ->
    Tree h p ->
    f (Tree h q)
htraverse f = hsequence . hmap (fmap MkContainedH . f)

-- | 'HTraversable' variant of 'traverse' for 'Hyper.Type.HyperType's with a single node type.
--
-- It is a valid 'Traversal' as it avoids using @RankNTypes@.
{-# INLINE htraverse1 #-}
htraverse1 ::
    (HTraversable h, HNodesConstraint h ((~) n)) =>
    Traversal (Tree h p) (Tree h q) (Tree p n) (Tree q n)
htraverse1 f = hsequence . (hmapped1 %~ (MkContainedH . f))
