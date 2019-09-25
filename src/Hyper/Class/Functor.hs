-- | A variant of 'Functor' for 'Hyper.Type.AHyperType's

module Hyper.Class.Functor
    ( HFunctor(..)
    , mappedH1
    ) where

import Control.Lens (Setter, sets)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))
import Data.Proxy (Proxy(..))
import Hyper.Class.Nodes
import Hyper.Type (Tree)

import Prelude.Compat

-- | A variant of 'Functor' for 'Hyper.Type.AHyperType's
class HNodes h => HFunctor h where
    -- | 'HFunctor' variant of 'fmap'
    --
    -- Applied a given mapping for @h@'s nodes (trees along witnesses that they are nodes of @h@)
    -- to result with a new tree, potentially with a different fix-point.
    mapH ::
        (forall n. HWitness h n -> Tree p n -> Tree q n) ->
        Tree h p ->
        Tree h q

instance HFunctor (Const a) where
    {-# INLINE mapH #-}
    mapH _ (Const x) = Const x

instance (HFunctor a, HFunctor b) => HFunctor (Product a b) where
    {-# INLINE mapH #-}
    mapH f (Pair x y) =
        Pair (mapH (f . E_Product_a) x) (mapH (f . E_Product_b) y)

instance (HFunctor a, HFunctor b) => HFunctor (Sum a b) where
    {-# INLINE mapH #-}
    mapH f (InL x) = InL (mapH (f . E_Sum_a) x)
    mapH f (InR x) = InR (mapH (f . E_Sum_b) x)

-- | 'HFunctor' variant of 'Control.Lens.mapped' for 'Hyper.Type.AHyperType's with a single node type.
--
-- Avoids using @RankNTypes@ and thus can be composed with other optics.
{-# INLINE mappedH1 #-}
mappedH1 ::
    forall h n p q.
    (HFunctor h, HNodesConstraint h ((~) n)) =>
    Setter (Tree h p) (Tree h q) (Tree p n) (Tree q n)
mappedH1 = sets (\f -> mapH (Proxy @((~) n) #> f))
