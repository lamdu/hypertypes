-- | 'AHyperType' is the 'Data.Kind.Kind' for nested higher-kinded data.
--
-- This library revolves around 'AHyperType's, which enable encoding many rich recursive structures.
--
-- For more information see the [README](https://github.com/lamdu/hypertypes/blob/master/README.md).

module Hyper.Type
    ( HyperType
    , AHyperType(..), GetHyperType
    , Tree, type (#)
    , asTree
    ) where

import Data.Kind (Type)

import Prelude.Compat

-- | A hypertype is a type parameterized by a hypertype
type HyperType = AHyperType -> Type

-- | A 'Data.Kind.Kind' for 'HyperType's
newtype AHyperType = AHyperType HyperType

-- | A type-level getter for the type constructor encoded in 'AHyperType'.
--
-- Notes:
--
-- * If @DataKinds@ supported lifting field getters this would had been replaced with the type's getter.
-- * 'GetHyperType' is injective, but due to no support for constrained type families,
--   [that's not expressible at the moment](https://ghc.haskell.org/trac/ghc/ticket/15691).
-- * Because 'GetHyperType' can't declared as bijective, uses of it may restrict inference.
--   In those cases wrapping terms with the 'asTree' helper assists Haskell's type inference
--   as if Haskell knew that 'GetHyperType' was bijective.
type family GetHyperType k where
    GetHyperType ('AHyperType t) = t

-- | A type synonym to express nested-HKD structures
type Tree k p = (k ('AHyperType p) :: Type)

-- | A type synonym to express child nodes in nested-HKDs
type k # p = Tree (GetHyperType k) p

-- | An 'id' variant which tells the type checker that its argument is a 'Tree'.
--
-- See the notes for 'GetHyperType' which expand on why this might be used.
--
-- Note that 'asTree' may often be used during development to assist the inference of incomplete code,
-- but removed once the code is complete.
asTree :: Tree k p -> Tree k p
asTree = id
