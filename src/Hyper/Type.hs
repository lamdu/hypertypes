-- | A 'HyperType' is a type parameterized by a hypertype.
--
-- This infinite definition is expressible using the 'AHyperType' 'Data.Kind.Kind' for hypertypes.
--
-- For more information see the [README](https://github.com/lamdu/hypertypes/blob/master/README.md).
module Hyper.Type
    ( HyperType
    , AHyperType (..)
    , GetHyperType
    , type (#)
    , type (:#)
    , asHyper
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
--   In those cases wrapping terms with the 'asHyper' helper assists Haskell's type inference
--   as if Haskell knew that 'GetHyperType' was bijective.
type family GetHyperType h where
    GetHyperType ('AHyperType t) = t

-- | A type synonym to express nested-HKD structures
type h # p = (h ('AHyperType p) :: Type)

-- | A type synonym to express child nodes in nested-HKDs
type h :# p = GetHyperType h # p

-- | An 'id' variant which tells the type checker that its argument is a hypertype.
--
-- See the notes for 'GetHyperType' which expand on why this might be used.
--
-- Note that 'asHyper' may often be used during development to assist the inference of incomplete code,
-- but removed once the code is complete.
asHyper :: h # p -> h # p
asHyper = id
