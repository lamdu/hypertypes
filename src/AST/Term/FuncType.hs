{-# LANGUAGE NoImplicitPrelude #-}

module AST.Term.FuncType
    ( FuncType(..)
    ) where

import           AST.Knot (Tree)
import           Control.Lens (Prism')

class FuncType t where
    funcType :: Prism' (Tree t f) (Tree f t, Tree f t)
