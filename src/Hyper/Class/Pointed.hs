-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.Knot's

module Hyper.Class.Pointed
    ( KPointed(..)
    ) where

import Hyper.Class.Nodes (KNodes(..), KWitness(..))
import Hyper.Type (Tree)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))

import Prelude.Compat

-- | A variant of 'Data.Pointed.Pointed' for 'Hyper.Type.Knot's
class KNodes k => KPointed k where
    -- | Construct a value from a generator of @k@'s nodes
    -- (a generator which can generate a tree of any type given a witness that it is a node of @k@)
    pureK ::
        (forall n. KWitness k n -> Tree p n) ->
        Tree k p

instance Monoid a => KPointed (Const a) where
    {-# INLINE pureK #-}
    pureK _ = Const mempty

instance (KPointed a, KPointed b) => KPointed (Product a b) where
    {-# INLINE pureK #-}
    pureK f = Pair (pureK (f . E_Product_a)) (pureK (f . E_Product_b))
