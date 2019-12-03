module Hyper.Combinator.Cont
    ( HCont(..), _HCont
    ) where

import Control.Lens (Iso, iso)
import Hyper.Type (HyperType, type (#))

-- TODO:
-- Is Cont the appropriate name for this combinator? or maybe HFunc?
newtype HCont (i :: HyperType) o h = HCont (i h -> o h)

_HCont ::
    Iso (HCont i0 o0 # h0)
        (HCont i1 o1 # h1)
        (i0 # h0 -> o0 # h0)
        (i1 # h1 -> o1 # h1)
_HCont = iso (\(HCont x) -> x) HCont
