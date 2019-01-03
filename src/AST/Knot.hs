{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies #-}

module AST.Knot
    ( Knot(..), RunKnot
    , Tie, Tree
    ) where

import Data.Kind (Type)

newtype Knot = Knot (Knot -> Type)
type family RunKnot (knot :: Knot) = (r :: Knot -> Type) where
    RunKnot ('Knot t) = t

type Tree k t = k ('Knot t)
type Tie knot ast = Tree (RunKnot knot) ast
