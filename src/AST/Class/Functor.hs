{-# LANGUAGE RankNTypes #-}

module AST.Class.Functor
    ( KFunctor(..)
    , mappedK1
    ) where

import AST.Class.Nodes
import AST.Knot (Tree)
import Control.Lens (Setter, sets)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A variant of 'Functor' for 'AST.Knot.Knot's
class KNodes k => KFunctor k where
    -- | 'KFunctor' variant of 'fmap'
    --
    -- Applied a given mapping for @k@'s nodes (trees along witnesses that they are nodes of @k@)
    -- to result with a new tree, potentially with a different fix-point.
    mapK ::
        (forall n. KWitness k n -> Tree p n -> Tree q n) ->
        Tree k p ->
        Tree k q

instance KFunctor (Const a) where
    {-# INLINE mapK #-}
    mapK _ (Const x) = Const x

instance (KFunctor a, KFunctor b) => KFunctor (Product a b) where
    {-# INLINE mapK #-}
    mapK f (Pair x y) =
        Pair (mapK (f . E_Product_a) x) (mapK (f . E_Product_b) y)

instance (KFunctor a, KFunctor b) => KFunctor (Sum a b) where
    {-# INLINE mapK #-}
    mapK f (InL x) = InL (mapK (f . E_Sum_a) x)
    mapK f (InR x) = InR (mapK (f . E_Sum_b) x)

-- | 'KFunctor' variant of 'Control.Lens.mapped' for 'AST.Knot.Knot's with a single node type.
--
-- Avoids using @RankNTypes@ and thus can be composed with other optics.
{-# INLINE mappedK1 #-}
mappedK1 ::
    forall k n p q.
    (KFunctor k, KNodesConstraint k ((~) n)) =>
    Setter (Tree k p) (Tree k q) (Tree p n) (Tree q n)
mappedK1 = sets (\f -> mapK (Proxy @((~) n) #> f))
