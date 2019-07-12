{-# LANGUAGE NoImplicitPrelude #-}

module AST.Combinator.Flip
    ( Flip(..), _Flip
    ) where

import           AST.Knot (Tree, RunKnot)
import qualified Control.Lens as Lens

-- Prefer _Flip to MkFlip because it has a friendlier type for
-- inference (without type families)
newtype Flip f x k = MkFlip (Tree (f (RunKnot k)) x)

_Flip ::
    Lens.Iso
    (Tree (Flip f0 x0) k0)
    (Tree (Flip f1 x1) k1)
    (Tree (f0 k0) x0)
    (Tree (f1 k1) x1)
_Flip = Lens.iso (\(MkFlip x) -> x) MkFlip
