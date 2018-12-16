{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies #-}

module AST.Knot
    ( Knot(..), RunKnot
    , Tie, Tree
    ) where

data Knot = Knot (Knot -> *)
type family RunKnot (knot :: Knot) :: Knot -> *
type instance RunKnot ('Knot t) = t

type Tie knot ast = RunKnot knot ('Knot ast)
type Tree k t = k ('Knot t)
