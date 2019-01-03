{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies #-}

module AST.Knot
    ( Knot(..), RunKnot
    , Tie, Tree
    ) where

import Data.Kind (Type)

newtype Knot = Knot (Knot -> Type)

type family RunKnot (knot :: Knot) = (r :: Knot -> Type) where
    RunKnot ('Knot t) = t

-- Notes about `RunKnot`:
-- * Its inputs are constrained to shape of `'Knot a`
-- * It is injective (`| r -> knot`), but due to no support for constrained type families it's not expressible atm:
--   (see https://ghc.haskell.org/trac/ghc/ticket/15691)

type Tree k t = k ('Knot t)
type Tie knot ast = Tree (RunKnot knot) ast
