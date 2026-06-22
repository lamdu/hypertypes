{-# LANGUAGE FlexibleContexts #-}

-- | A class for plain 'Data.Kind.Type' equivalents
-- for the simple forms of 'Hyper.Type.HyperType's.
--
-- Useful for succinct tests, examples, and for debug prints.
module Hyper.Class.HasPlain
    ( HasHPlain (..)
    , hPlain'
    ) where

import Control.Lens (Iso')
import qualified Control.Lens as Lens
import Hyper.Internal.Prelude
import Hyper.Type (type (#))
import Hyper.Type.Pure (Pure (..), _Pure)

-- | A class for a plain form of a @Pure # h@
class Show (HPlain h) => HasHPlain h where
    -- | Plain form data type
    data HPlain h

    -- | An 'Control.Lens.Iso' between the plain form and 'Hyper.Type.HyperType' form
    hPlain :: Iso' (HPlain h) (Pure # h)

hPlain' :: HasHPlain h => Iso' (HPlain h) (h # Pure)
hPlain' = hPlain . _Pure

instance Show a => HasHPlain (Const a) where
    newtype HPlain (Const a) = ConstP a
        deriving (Show)
    hPlain =
        _hPlainConst . Lens._Unwrapped . Lens.from _Pure
        where
            -- TODO: Replace with Lens._Unwrapped?
            _hPlainConst :: Iso' (HPlain (Const a)) a
            _hPlainConst = Lens.iso (\(ConstP x) -> x) ConstP
