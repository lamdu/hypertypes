{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module AST.Class.Functor
    ( KFunctor(..)
    , mapK1
    ) where

import AST.Class
import AST.Knot (Tree)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Proxy (Proxy(..))

class KNodes k => KFunctor k where
    mapK ::
        (forall c. Tree m c -> Tree n c) ->
        Tree k m ->
        Tree k n

    mapKWith ::
        NodesConstraint k constraint =>
        Proxy constraint ->
        (forall c. constraint c => Tree m c -> Tree n c) ->
        Tree k m ->
        Tree k n

instance KFunctor (Const a) where
    {-# INLINE mapK #-}
    mapK _ (Const x) = Const x
    {-# INLINE mapKWith #-}
    mapKWith _ _ (Const x) = Const x

instance (KFunctor a, KFunctor b) => KFunctor (Product a b) where
    {-# INLINE mapK #-}
    mapK f (Pair x y) = Pair (mapK f x) (mapK f y)
    {-# INLINE mapKWith #-}
    mapKWith p f (Pair x y) =
        Pair (mapKWith p f x) (mapKWith p f y)

{-# INLINE mapK1 #-}
mapK1 ::
    forall k c m n.
    (KFunctor k, NodesConstraint k ((~) c)) =>
    (Tree m c -> Tree n c) ->
    Tree k m ->
    Tree k n
mapK1 = mapKWith (Proxy @((~) c))
