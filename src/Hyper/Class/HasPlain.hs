-- | A class for plain `Data.Kind.Type` equivalents
-- for the simple forms of 'Hyper.Knot.Knot's.
--
-- Useful for succinct tests, examples, and for debug prints.

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.HasPlain
    ( KHasPlain(..)
    ) where

import Hyper.Knot (Tree)
import Hyper.Knot.Pure (Pure)
import Control.Lens (Iso')

import Prelude.Compat

-- | A class for a plain for of a @Tree Pure k@
class Show (KPlain k) => KHasPlain k where
    -- | Plain form data type
    data KPlain k
    -- | An 'Control.Lens.Iso' between the plain and knotted forms
    kPlain :: Iso' (KPlain k) (Tree Pure k)
