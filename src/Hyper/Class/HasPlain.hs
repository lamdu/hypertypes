-- | A class for plain `Data.Kind.Type` equivalents
-- for the simple forms of 'Hyper.Type.AHyperType's.
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

-- | A class for a plain for of a @Tree Pure k@
class Show (HPlain k) => HasHPlain k where
    -- | Plain form data type
    data HPlain k
    -- | An 'Control.Lens.Iso' between the plain form and 'Hyper.Type.HyperType' form
    kPlain :: Iso' (HPlain k) (Tree Pure k)
