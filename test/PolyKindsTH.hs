{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Regression test for deriving nodes for types with polykinded parameters.
--
-- See https://github.com/lamdu/hypertypes/issues/23
module PolyKindsTH where

import Hyper.TH.Nodes (makeHNodes)
import Hyper.Type (type (:#))

newtype Foo x h = Foo (h :# Foo x)

makeHNodes ''Foo
