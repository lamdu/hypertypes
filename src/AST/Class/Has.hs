module AST.Class.Has
    ( HasChild(..)
    ) where

import AST.Knot (Tree)
import Control.Lens (Lens')

-- | @HasChild record child@ represents that @record@ has exactly one child node of @child@.
--
-- Useful for records of values for several different types,
-- for example when performing unification of heterogenous ASTs,
-- the @record@ 'AST.Knot.Knot' can be used to hold the unification variables mappings
-- for each of the types in the AST.
class HasChild record child where
    -- | A 'Control.Lens.Lens' from the record to the child node
    getChild :: Lens' (Tree record k) (Tree k child)
