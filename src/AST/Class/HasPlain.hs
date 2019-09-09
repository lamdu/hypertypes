{-# LANGUAGE FlexibleContexts #-}

module AST.Class.HasPlain
    ( KHasPlain(..)
    ) where

import AST.Knot (Tree)
import AST.Knot.Pure (Pure)
import Control.Lens (Iso')

import Prelude.Compat

class Show (KPlain k) => KHasPlain k where
    data KPlain k
    kPlain :: Iso' (KPlain k) (Tree Pure k)
