{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Compile-time regression test for deriving instances for fields whose types
-- are hidden behind type synonyms.
--
-- See https://github.com/lamdu/hypertypes/issues/35
module TypeSynonymsTH where

import Hyper
import Hyper.TH.Nodes (makeHNodes)

type Bar = Pure :*: Pure
newtype Foo h = Foo (Bar h)

makeHNodes ''Foo
