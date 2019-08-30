module AST.Knot
    ( Knot(..), RunKnot
    , Tree, Node
    , asTree
    ) where

import Data.Kind (Type)

import Prelude.Compat

-- | A 'Data.Kind.Kind' for nested higher-kinded data.
--
-- This library revolves around 'Knot's, which enable encoding many rich recursive structures.
--
-- For more information see the [README](https://github.com/lamdu/syntax-tree/blob/master/README.md).
newtype Knot = Knot (Knot -> Type)

-- | A type-level getter for the type constructor encoded in 'Knot'.
--
-- Notes:
--
-- * If `DataKinds` supported lifting field getters this would had been replaced with the type's getter.
-- * 'RunKnot' is injective, but due to no support for constrained type families,
--   [that's not expressible at the moment](https://ghc.haskell.org/trac/ghc/ticket/15691).
-- * Because `RunKnot` can't declared as bijective, uses of it may restrict inference.
--   In those cases wrapping terms with the 'asTree' helper assists Haskell's type inference
--   as if Haskell knew that 'RunKnot' was bijective.
type family RunKnot (k :: Knot) = (r :: Knot -> Type) where
    RunKnot ('Knot t) = t

-- | A type synonym to express nested-HKD structures
type Tree k t = (k ('Knot t) :: Type)

-- | A type synonym to express child nodes in nested-HKDs
type Node knot ast = Tree (RunKnot knot) ast

-- | An 'id' variant which tells the type checker that its argument is a 'Tree'.
--
-- See the notes for 'RunKnot' which expand on why this might be used.
--
-- Note that 'asTree' may often be used during development to assist the inference of incomplete code,
-- but removed once the code is complete.
asTree :: Tree p q -> Tree p q
asTree = id
