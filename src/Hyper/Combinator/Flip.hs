{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A combinator to flip the order of the last two type parameters of a 'Hyper.Type.HyperType'.
module Hyper.Combinator.Flip
    ( HFlip (..)
    , _HFlip
    , hflipped
    , htraverseFlipped
    ) where

import Control.Lens (from, iso)
import Hyper.Class.Nodes (HWitness)
import Hyper.Class.Traversable (HTraversable, htraverse)
import Hyper.Type (GetHyperType, type (#))

import Hyper.Internal.Prelude

-- | Flip the order of the last two type parameters of a 'Hyper.Type.HyperType'.
--
-- Useful to use instances of classes such as 'Hyper.Class.Traversable.HTraversable' which
-- are available on the flipped 'Hyper.Type.HyperType'.
-- For example 'Hyper.Unify.Generalize.GTerm' has instances when flipped.
newtype HFlip f x h
    = MkHFlip (f (GetHyperType h) # x)
    deriving stock (Generic)

makeCommonInstances [''HFlip]

-- | An 'Iso' from 'Flip' to its content.
--
-- Using `_Flip` rather than the 'MkFlip' data constructor is recommended,
-- because it helps the type inference know that @ANode c@ is parameterized with a 'Hyper.Type.HyperType'.
_HFlip ::
    Iso
        (HFlip f0 x0 # k0)
        (HFlip f1 x1 # k1)
        (f0 k0 # x0)
        (f1 k1 # x1)
_HFlip = iso (\(MkHFlip x) -> x) MkHFlip

hflipped ::
    Iso
        (f0 k0 # x0)
        (f1 k1 # x1)
        (HFlip f0 x0 # k0)
        (HFlip f1 x1 # k1)
hflipped = from _HFlip

-- | Convinience function for traversal over second last 'HyperType' argument.
htraverseFlipped ::
    (Applicative f, HTraversable (HFlip h a)) =>
    (forall n. HWitness (HFlip h a) n -> p # n -> f (q # n)) ->
    h p # a ->
    f (h q # a)
htraverseFlipped f = hflipped (htraverse f)
