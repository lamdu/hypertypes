-- | A class for records holding a single element of a given type.
--
-- Useful for records of values for several different types,
-- for example when performing unification of heterogenous ASTs,
-- the @record@ 'AST.Knot.Knot' can be used to hold the unification variables mappings
-- for each of the AST types.

module AST.Class.Has
    ( HasChild(..)
    ) where

import AST.Knot (Tree)
import Control.Lens (Lens')

-- | @HasChild record child@ represents that @record@ has exactly one child node of @child@
class HasChild record child where
    -- | A 'Control.Lens.Lens' from the record to the child node
    getChild :: Lens' (Tree record k) (Tree k child)
