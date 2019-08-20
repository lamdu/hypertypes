module AST.Class.Has
    ( HasChild(..)
    ) where

import AST.Knot (Tree)
import Control.Lens (Lens')

-- | When `record` has exactly one child of type `typ`, `HasChild`
-- provides a lens to access it
class HasChild record typ where
    getChild :: Lens' (Tree record k) (Tree k typ)
