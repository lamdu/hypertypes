-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.AHyperType's

module Hyper.Class.Pointed
    ( HPointed(..)
    ) where

import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Hyper.Class.Nodes (HNodes(..), HWitness(..))
import Hyper.Type (Tree)

import Prelude.Compat

-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.AHyperType's
class HNodes h => HPointed h where
    -- | Construct a value from a generator of @h@'s nodes
    -- (a generator which can generate a tree of any type given a witness that it is a node of @h@)
    pureK ::
        (forall n. HWitness h n -> Tree p n) ->
        Tree h p

instance Monoid a => HPointed (Const a) where
    {-# INLINE pureK #-}
    pureK _ = Const mempty

instance (HPointed a, HPointed b) => HPointed (Product a b) where
    {-# INLINE pureK #-}
    pureK f = Pair (pureK (f . E_Product_a)) (pureK (f . E_Product_b))
