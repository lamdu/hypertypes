-- | A class for records holding a single element of a given type.
--
-- Useful for records of values for several different types,
-- for example when performing unification of heterogenous ASTs,
-- the @record@ 'Hyper.Type.HyperType' can be used to hold the unification variables mappings
-- for each of the AST types.

module Hyper.Class.Has
    ( HasChild(..)
    ) where

import Control.Lens (Lens')
import Hyper.Type (Tree)

-- | @HasChild record child@ represents that @record@ has exactly one child node of @child@
class HasChild record child where
    -- | A 'Control.Lens.Lens' from the record to the child node
    getChild :: Lens' (Tree record h) (Tree h child)
