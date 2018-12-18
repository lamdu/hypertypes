{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies #-}

module AST.Knot
    ( Knot(..), RunKnot
    , Tie, Tree
    ) where

import Data.Kind (Type)

newtype Knot = Knot (Knot -> Type)
type family RunKnot (knot :: Knot) :: Knot -> Type
type instance RunKnot ('Knot t) = t

type Tie knot ast = RunKnot knot ('Knot ast)
type Tree k t = k ('Knot t)
