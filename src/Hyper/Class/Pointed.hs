-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.AHyperType's

module Hyper.Class.Pointed
    ( HPointed(..)
    ) where

import Hyper.Class.Nodes (HNodes(..), HWitness(..))
import Hyper.Type (Tree)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))

import Prelude.Compat

-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.AHyperType's
class HNodes k => HPointed k where
    -- | Construct a value from a generator of @k@'s nodes
    -- (a generator which can generate a tree of any type given a witness that it is a node of @k@)
    pureK ::
        (forall n. HWitness k n -> Tree p n) ->
        Tree k p

instance Monoid a => HPointed (Const a) where
    {-# INLINE pureK #-}
    pureK _ = Const mempty

instance (HPointed a, HPointed b) => HPointed (Product a b) where
    {-# INLINE pureK #-}
    pureK f = Pair (pureK (f . E_Product_a)) (pureK (f . E_Product_b))
