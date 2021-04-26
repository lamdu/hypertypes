{-# LANGUAGE TemplateHaskell #-}
module LangD where

import           Hyper
import           Hyper.TH.Functor
import           Hyper.TH.Nodes

newtype A i k = A (B i k)
newtype B i k = B (i (k :# A i))

makeHNodes ''A
makeHNodes ''B

-- The following does not compile
-- makeHFunctor ''A

makeHFunctor ''B
