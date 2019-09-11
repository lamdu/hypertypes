-- | 'Knot' is the 'Data.Kind.Kind' for nested higher-kinded data.
--
-- This library revolves around 'Knot's, which enable encoding many rich recursive structures.
--
-- For more information see the [README](https://github.com/lamdu/syntax-tree/blob/master/README.md).

module AST.Knot
    ( Knot(..), GetKnot
    , Tree, type (#)
    , asTree
    ) where

import Data.Kind (Type)

import Prelude.Compat

-- | A 'Data.Kind.Kind' for nested higher-kinded data.
newtype Knot = Knot (Knot -> Type)

-- | A type-level getter for the type constructor encoded in 'Knot'.
--
-- Notes:
--
-- * If @DataKinds@ supported lifting field getters this would had been replaced with the type's getter.
-- * 'GetKnot' is injective, but due to no support for constrained type families,
--   [that's not expressible at the moment](https://ghc.haskell.org/trac/ghc/ticket/15691).
-- * Because 'GetKnot' can't declared as bijective, uses of it may restrict inference.
--   In those cases wrapping terms with the 'asTree' helper assists Haskell's type inference
--   as if Haskell knew that 'GetKnot' was bijective.
type family GetKnot k where
    GetKnot ('Knot t) = t

-- | A type synonym to express nested-HKD structures
type Tree k p = (k ('Knot p) :: Type)

-- | A type synonym to express child nodes in nested-HKDs
type k # p = Tree (GetKnot k) p

-- | An 'id' variant which tells the type checker that its argument is a 'Tree'.
--
-- See the notes for 'GetKnot' which expand on why this might be used.
--
-- Note that 'asTree' may often be used during development to assist the inference of incomplete code,
-- but removed once the code is complete.
asTree :: Tree k p -> Tree k p
asTree = id
