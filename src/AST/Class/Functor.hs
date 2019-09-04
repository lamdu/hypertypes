{-# LANGUAGE RankNTypes #-}

module AST.Class.Functor
    ( KFunctor(..)
    , mapKWith, mapKWithWitness
    , mappedK1
    ) where

import AST.Class.Nodes
import AST.Knot (Knot, RunKnot, Tree)
import Control.Lens (Setter, sets)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
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
        Pair (mapK (f . KWitness_Product_E0) x) (mapK (f . KWitness_Product_E1) y)

newtype MapK p q (c :: Knot) = MapK { getMapK :: p c -> q c }

-- | Variant of 'mapK' for functions with context instead of a witness parameter
{-# INLINE mapKWith #-}
mapKWith ::
    (KFunctor k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall n. constraint n => Tree p n -> Tree q n) ->
    Tree k p ->
    Tree k q
mapKWith p f = mapK (\w -> getMapK (kLiftConstraint w p (MapK f)))

newtype MapKW k p q n = MapKW { getMapKW :: KWitness k (RunKnot n) -> p n -> q n }

-- | Variant of 'mapKWith' which provides a witness parameter in addition to the context
{-# INLINE mapKWithWitness #-}
mapKWithWitness ::
    (KFunctor k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall n. constraint n => KWitness k n -> Tree p n -> Tree q n) ->
    Tree k p ->
    Tree k q
mapKWithWitness p f = mapK (\w -> getMapKW (kLiftConstraint w p (MapKW f)) w)

-- | 'KFunctor' variant of 'Control.Lens.mapped' for 'AST.Knot.Knot's with a single node type.
--
-- Avoids using @RankNTypes@ and thus can be composed with other optics.
{-# INLINE mappedK1 #-}
mappedK1 ::
    forall k n p q.
    (KFunctor k, NodesConstraint k ((~) n)) =>
    Setter (Tree k p) (Tree k q) (Tree p n) (Tree q n)
mappedK1 = sets (mapKWith (Proxy @((~) n)))
