module AST.Combinator.Flip
    ( Flip(..), _Flip
    ) where

import           AST.Knot (Tree, RunKnot)
import qualified Control.Lens as Lens

-- | Flip the order of the last two type type parameters of a 'AST.Knot.Knot'.
--
-- Useful to use instances of classes such as 'AST.Class.Traversable.KTraversable' which
-- are available on the flipped knot.
-- For example 'AST.Unify.Generalize.GTerm' has instances when flipped.
newtype Flip f x k = MkFlip (Tree (f (RunKnot k)) x)

-- | An 'Iso' from 'Flip' to its content.
--
-- Using `_Flip` rather than the 'MkFlip' data constructor is recommended,
-- because it helps the type inference know that @ANode c@ is parameterized with a 'AST.Knot.Knot'
_Flip ::
    Lens.Iso
    (Tree (Flip f0 x0) k0)
    (Tree (Flip f1 x1) k1)
    (Tree (f0 k0) x0)
    (Tree (f1 k1) x1)
_Flip = Lens.iso (\(MkFlip x) -> x) MkFlip
