module Hyper.Combinator.Cont
    ( HCont(..), _HCont
    ) where

import Control.Lens (Iso, iso)
import Hyper.Type (HyperType, type (#))

newtype HCont r (p :: HyperType) h = HCont (p h -> r h)

_HCont ::
    Iso (HCont r0 p0 # h0)
        (HCont r1 p1 # h1)
        (p0 # h0 -> r0 # h0)
        (p1 # h1 -> r1 # h1)
_HCont = iso (\(HCont x) -> x) HCont
