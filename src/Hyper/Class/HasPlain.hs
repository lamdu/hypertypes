-- | A class for plain 'Data.Kind.Type' equivalents
-- for the simple forms of 'Hyper.Type.HyperType's.
--
-- Useful for succinct tests, examples, and for debug prints.

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.HasPlain
    ( HasHPlain(..)
    ) where

import Control.Lens (Iso')
import Hyper.Type (Tree)
import Hyper.Type.Pure (Pure)

import Prelude.Compat

-- | A class for a plain for of a @Tree Pure h@
class Show (HPlain h) => HasHPlain h where
    -- | Plain form data type
    data HPlain h
    -- | An 'Control.Lens.Iso' between the plain form and 'Hyper.Type.HyperType' form
    hPlain :: Iso' (HPlain h) (Tree Pure h)
