{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

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
import GHC.Generics as X ((:+:) (..))
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

instance (Show (HPlain (a :*: b)), HasHPlain a, HasHPlain b) => HasHPlain (a :*: b) where
    data HPlain (a :*: b) = ProdP (HPlain a) (HPlain b)
    hPlain =
        Lens.iso
        (\(ProdP a b) -> Pure (a ^. hPlain' :*: b ^. hPlain'))
        (\(Pure (a :*: b)) -> ProdP (hPlain' # a) (hPlain' # b))

deriving instance (Show (HPlain a), Show (HPlain b)) => Show (HPlain (a :*: b))

instance (Show (HPlain (a :+: b)), HasHPlain a, HasHPlain b) => HasHPlain (a :+: b) where
    data HPlain (a :+: b) = L1P (HPlain a) | R1P (HPlain b)
    hPlain =
        Lens.iso fromPlain toPlain . Lens.from _Pure
        where
            fromPlain (L1P a) = L1 (a ^. hPlain')
            fromPlain (R1P b) = R1 (b ^. hPlain')
            toPlain (L1 a) = L1P (hPlain' # a)
            toPlain (R1 b) = R1P (hPlain' # b)

deriving instance (Show (HPlain a), Show (HPlain b)) => Show (HPlain (a :+: b))
