-- TODO: Better naming

{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses #-}

module AST.Class.HasChild
    ( HasChild(..)
    ) where

import AST.Knot (Tree)
import Control.Lens (Lens')

class HasChild record typ where
    getChild :: Lens' (Tree record k) (Tree k typ)
