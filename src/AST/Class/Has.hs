{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleInstances #-}

module AST.Class.Has
    ( KHas(..), HasChild(..)
    ) where

import AST.Knot (Tree)
import Control.Lens (Lens')
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))

import Prelude.Compat

-- | A uni-directional version of `Has` from `data-has`.
-- Used to translated `NodeTypesOf` instances.

class KHas dst src where
    hasK :: Tree src k -> Tree dst k

instance KHas k k where
    hasK = id

-- Useful instance for when a type has a single child type,
-- but uses a parameterized AST term which may have two different types.
instance KHas (Product k k) k where
    hasK x = Pair x x

instance Monoid a => KHas (Const a) k where
    hasK _ = Const mempty

-- | When `record` has exactly one child of type `typ`, `HasChild`
-- provides a lens to access it
class HasChild record typ where
    getChild :: Lens' (Tree record k) (Tree k typ)
