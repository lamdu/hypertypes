module Hyper.Combinator.Func
    ( HFunc(..), _HFunc
    ) where

import Control.Lens (Iso, iso)
import Hyper.Type (HyperType, type (#))

newtype HFunc (i :: HyperType) o h = HFunc (i h -> o h)

_HFunc ::
    Iso (HFunc i0 o0 # h0)
        (HFunc i1 o1 # h1)
        (i0 # h0 -> o0 # h0)
        (i1 # h1 -> o1 # h1)
_HFunc = iso (\(HFunc x) -> x) HFunc
