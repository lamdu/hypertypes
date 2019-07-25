{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleInstances #-}

module AST.Class.Has
    ( KHas(..)
    ) where

import AST.Knot (Tree)

import Prelude.Compat

-- | A uni-directional version of `Has` from `data-has`.
-- Used to translated `NodeTypesOf` instances.

class KHas dst src where
    hasK :: Tree src k -> Tree dst k

instance KHas k k where
    hasK = id
