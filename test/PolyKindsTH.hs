{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Regression test for deriving nodes for types with polykinded parameters.
--
-- See https://github.com/lamdu/hypertypes/issues/23
module PolyKindsTH where

import Hyper.TH.Nodes (makeHNodes)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (type (#), type (:#))

newtype Foo x h = Foo (h :# Foo x)

makeHNodes ''Foo

data GadtNode h where
    GadtNode :: child # GadtNode -> GadtNode # child

makeHTraversableApplyAndBases ''GadtNode
