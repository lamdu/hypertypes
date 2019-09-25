-- | A combinator to flip the order of the last two type parameters of a 'Hyper.Type.AHyperType'.

module Hyper.Type.Combinator.Flip
    ( Flip(..), _Flip
    ) where

import Control.Lens (Iso, iso)
import Hyper.Type (Tree, GetHyperType)

-- | Flip the order of the last two type parameters of a 'Hyper.Type.AHyperType'.
--
-- Useful to use instances of classes such as 'Hyper.Class.Traversable.HTraversable' which
-- are available on the flipped 'Hyper.Type.HyperType'.
-- For example 'Hyper.Unify.Generalize.GTerm' has instances when flipped.
newtype Flip f x h = MkFlip (Tree (f (GetHyperType h)) x)

-- | An 'Iso' from 'Flip' to its content.
--
-- Using `_Flip` rather than the 'MkFlip' data constructor is recommended,
-- because it helps the type inference know that @ANode c@ is parameterized with a 'Hyper.Type.AHyperType'.
_Flip ::
    Iso
    (Tree (Flip f0 x0) k0)
    (Tree (Flip f1 x1) k1)
    (Tree (f0 k0) x0)
    (Tree (f1 k1) x1)
_Flip = iso (\(MkFlip x) -> x) MkFlip
