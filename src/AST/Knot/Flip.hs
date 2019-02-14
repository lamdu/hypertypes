{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds #-}

module AST.Knot.Flip
    ( Flip(..), _Flip
    ) where

import AST.Knot (Knot(..), RunKnot)
import Control.Lens (makePrisms)

newtype Flip k x y = Flip (k (RunKnot y) ('Knot x))
makePrisms ''Flip
