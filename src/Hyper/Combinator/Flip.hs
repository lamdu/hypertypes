-- | A combinator to flip the order of the last two type parameters of a 'Hyper.Knot.Knot'.

module Hyper.Combinator.Flip
    ( Flip(..), _Flip
    ) where

import Hyper.Knot (Tree, GetKnot)
import Control.Lens (Iso, iso)

-- | Flip the order of the last two type parameters of a 'Hyper.Knot.Knot'.
--
-- Useful to use instances of classes such as 'Hyper.Class.Traversable.KTraversable' which
-- are available on the flipped knot.
-- For example 'Hyper.Unify.Generalize.GTerm' has instances when flipped.
newtype Flip f x k = MkFlip (Tree (f (GetKnot k)) x)

-- | An 'Iso' from 'Flip' to its content.
--
-- Using `_Flip` rather than the 'MkFlip' data constructor is recommended,
-- because it helps the type inference know that @ANode c@ is parameterized with a 'Hyper.Knot.Knot'.
_Flip ::
    Iso
    (Tree (Flip f0 x0) k0)
    (Tree (Flip f1 x1) k1)
    (Tree (f0 k0) x0)
    (Tree (f1 k1) x1)
_Flip = iso (\(MkFlip x) -> x) MkFlip
