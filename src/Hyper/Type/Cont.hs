module Hyper.Type.Cont
    ( HCont(..)
    ) where

import Control.Lens (Iso, iso)
import Hyper.Type (HyperType, Tree)

newtype HCont r (p :: HyperType) h = HCont (p h -> r)

_HCont ::
    Iso (Tree (HCont r0 p0) h0)
        (Tree (HCont r1 p1) h1)
        (Tree p0 h0 -> r0)
        (Tree p1 h1 -> r1)
_HCont = iso (\(HCont x) -> x) HCont
