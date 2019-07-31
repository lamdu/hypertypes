{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleInstances #-}

module AST.Class.Has
    ( KHas(..), HasChild(..)
    ) where

import AST.Knot (Tree)
import Control.Lens (Lens')

import Prelude.Compat

-- | A uni-directional version of `Has` from `data-has`.
-- Used to translated `NodeTypesOf` instances.

class KHas dst src where
    hasK :: Tree src k -> Tree dst k

instance KHas k k where
    hasK = id

-- | When `record` has exactly one child of type `typ`, `HasChild`
-- provides a lens to access it
class HasChild record typ where
    getChild :: Lens' (Tree record k) (Tree k typ)
