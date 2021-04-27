{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}
module LangD where

import           Hyper
import           Hyper.TH.Functor
import           Hyper.TH.Nodes

newtype A i k = A (B i k)
newtype B i k = B (i (k :# A i))

makeHNodes ''A
makeHNodes ''B

makeHFunctor ''B
makeHFunctor ''A
