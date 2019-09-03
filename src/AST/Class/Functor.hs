{-# LANGUAGE RankNTypes #-}

module AST.Class.Functor
    ( KFunctor(..)
    , mapKWith, mapKWithWitness
    , mappedK1
    ) where

import AST.Class.Nodes
import AST.Knot (Knot, RunKnot, Tree)
import Control.Monad (join)
import Control.Lens (Setter, sets)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A variant of 'Functor' for 'AST.Knot.Knot's
class KNodes k => KFunctor k where
    -- | 'KFunctor' variant of 'fmap'
    mapK ::
        (forall c. KWitness k c -> Tree m c -> Tree n c) ->
        Tree k m ->
        Tree k n

instance KFunctor (Const a) where
    {-# INLINE mapK #-}
    mapK _ (Const x) = Const x

instance (KFunctor a, KFunctor b) => KFunctor (Product a b) where
    {-# INLINE mapK #-}
    mapK f (Pair x y) =
        Pair (mapK (f . KWitness_Product_E0) x) (mapK (f . KWitness_Product_E1) y)

newtype MapK m n (c :: Knot) = MapK { getMapK :: m c -> n c }

{-# INLINE mapKWith #-}
mapKWith ::
    (KFunctor k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree m c -> Tree n c) ->
    Tree k m ->
    Tree k n
mapKWith p f = mapK (getMapK . kLiftConstraint p (MapK f))

newtype MapKW k m n c = MapKW { getMapKW :: KWitness k (RunKnot c) -> m c -> n c }

{-# INLINE mapKWithWitness #-}
mapKWithWitness ::
    (KFunctor k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => KWitness k c -> Tree m c -> Tree n c) ->
    Tree k m ->
    Tree k n
mapKWithWitness p f = mapK (join (getMapKW . kLiftConstraint p (MapKW f)))

-- | 'KFunctor' variant of 'Control.Lens.mapped' for 'AST.Knot.Knot's with a single node type.
--
-- Avoids using @RankNTypes@ and thus can be composed with other optics.
{-# INLINE mappedK1 #-}
mappedK1 ::
    forall k c m n.
    (KFunctor k, NodesConstraint k ((~) c)) =>
    Setter (Tree k m) (Tree k n) (Tree m c) (Tree n c)
mappedK1 = sets (mapKWith (Proxy @((~) c)))
