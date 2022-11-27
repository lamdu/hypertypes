{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.Optic
    ( HNodeLens (..)
    , HSubset (..)
    , HSubset'
    ) where

import Control.Lens (Lens', Prism)
import Hyper.Type (type (#))

class HNodeLens s a where
    hNodeLens :: Lens' (s # h) (h # a)

class HSubset s t a b where
    hSubset :: Prism (s # h) (t # h) (a # h) (b # h)

type HSubset' s a = HSubset s s a a
