-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.HyperType's

module Hyper.Class.Pointed
    ( HPointed(..)
    ) where

import GHC.Generics ((:+:)(..))
import Hyper.Class.Nodes (HNodes, HWitness(..))
import Hyper.Type (type (#))

import Hyper.Internal.Prelude

-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.HyperType's
class HNodes h => HPointed h where
    -- | Construct a value from a generator of @h@'s nodes
    -- (a generator which can generate a tree of any type given a witness that it is a node of @h@)
    hpure ::
        (forall n. HWitness h n -> p # n) ->
        h # p

instance Monoid a => HPointed (Const a) where
    {-# INLINE hpure #-}
    hpure _ = Const mempty

instance (HPointed a, HPointed b) => HPointed (a :*: b) where
    {-# INLINE hpure #-}
    hpure f = hpure (f . HWitness . L1) :*: hpure (f . HWitness . R1)
