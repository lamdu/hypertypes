{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}
module LangD where

import Hyper

newtype A i k = A (B i k)
newtype B i k = B (i (k :# A i))

-- Note that the order of these two is important,
-- as the derivations for A learn the constraints from the previously generated instances of B.
makeHTraversableApplyAndBases ''B
makeHTraversableApplyAndBases ''A

newtype C (k :: AHyperType) = C (C k)
-- The following doesn't work:
-- makeHNodes ''C
