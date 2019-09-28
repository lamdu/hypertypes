-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.HyperType's

module Hyper.Class.Pointed
    ( HPointed(..)
    ) where

import Data.Functor.Const (Const(..))
import GHC.Generics ((:*:)(..), (:+:)(..))
import Hyper.Class.Nodes (HNodes, HWitness(..))
import Hyper.Type (Tree)

import Prelude.Compat

-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.HyperType's
class HNodes h => HPointed h where
    -- | Construct a value from a generator of @h@'s nodes
    -- (a generator which can generate a tree of any type given a witness that it is a node of @h@)
    hpure ::
        (forall n. HWitness h n -> Tree p n) ->
        Tree h p

instance Monoid a => HPointed (Const a) where
    {-# INLINE hpure #-}
    hpure _ = Const mempty

instance (HPointed a, HPointed b) => HPointed (a :*: b) where
    {-# INLINE hpure #-}
    hpure f = hpure (f . HWitness . L1) :*: hpure (f . HWitness . R1)
