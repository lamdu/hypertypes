{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies #-}

module AST.Knot.Functor
    ( ToKnot(..)
    ) where

import AST.Class.Recursive.TH (makeChildrenRecursive)
import AST.Knot (Tie)

newtype ToKnot f k = ToKnot { getToKnot :: f (Tie k (ToKnot f)) }

makeChildrenRecursive [''ToKnot]
