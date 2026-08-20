{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Regression test for deriving nodes for types with polykinded parameters.
--
-- See https://github.com/lamdu/hypertypes/issues/23
module PolyKindsTH where

import Hyper.Combinator.Flip (HFlip)
import Hyper.TH.Generic (makeGeneric)
import Hyper.TH.Nodes (makeHNodes)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (type (#), type (:#))
import Prelude (Bool, Int, Maybe)

newtype Foo x h = Foo (h :# Foo x)

makeHNodes ''Foo

data GadtNode h where
    GadtNode :: child # GadtNode -> GadtNode # child

makeHTraversableApplyAndBases ''GadtNode

data GenericGadt h where
    GadtLeaf :: GenericGadt # child
    GadtFields :: child # GenericGadt -> Int -> GenericGadt # child
    GadtAlternative :: Bool -> child # GenericGadt -> GenericGadt # child

makeGeneric ''GenericGadt

newtype EmbeddedGadt f x h = EmbeddedGadt (Maybe (HFlip f x h))

makeHTraversableApplyAndBases ''EmbeddedGadt
