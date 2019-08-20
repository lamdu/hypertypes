{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}

module AST.Class
    ( KNodes(..)
    , KPointed(..)
    , KFunctor(..)
    , KApply(..)
    , KApplicative
    , mapK1
    , liftK2, liftK2With
    ) where

import AST.Knot (Knot, Tree)
import Data.Constraint
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Constraint.List (And)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class KNodes (k :: Knot -> Type) where
    -- | Lift a constraint to apply to the node types.
    type family NodesConstraint k (c :: ((Knot -> Type) -> Constraint)) :: Constraint

    kCombineConstraints ::
        (NodesConstraint k a, NodesConstraint k b) =>
        Proxy (And a b k) ->
        Dict (NodesConstraint k (And a b))

class KNodes k => KPointed k where
    -- | Construct a value from a higher ranked child value
    pureK ::
        (forall child. Tree n child) ->
        Tree k n

    -- | Construct a value from a higher ranked child value with a constraint
    pureKWith ::
        NodesConstraint k constraint =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child) ->
        Tree k n

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

class KFunctor k => KApply k where
    -- | Combine child values given a combining function per child type
    zipK ::
        Tree k a ->
        Tree k b ->
        Tree k (Product a b)

class    (KPointed k, KApply k) => KApplicative k
instance (KPointed k, KApply k) => KApplicative k

instance KNodes (Const a) where
    type NodesConstraint (Const a) x = ()
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = Dict

instance Monoid a => KPointed (Const a) where
    {-# INLINE pureK #-}
    pureK _ = Const mempty
    {-# INLINE pureKWith #-}
    pureKWith _ _ = Const mempty

instance KFunctor (Const a) where
    {-# INLINE mapK #-}
    mapK _ (Const x) = Const x
    {-# INLINE mapKWith #-}
    mapKWith _ _ (Const x) = Const x

instance Semigroup a => KApply (Const a) where
    {-# INLINE zipK #-}
    zipK (Const x) (Const y) = Const (x <> y)

instance (KNodes a, KNodes b) => KNodes (Product a b) where
    type NodesConstraint (Product a b) x = (NodesConstraint a x, NodesConstraint b x)
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p =
        withDict (kCombineConstraints (p0 p)) $
        withDict (kCombineConstraints (p1 p)) Dict
        where
            p0 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 a)
            p0 _ = Proxy
            p1 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 b)
            p1 _ = Proxy

instance (KPointed a, KPointed b) => KPointed (Product a b) where
    {-# INLINE pureK #-}
    pureK f = Pair (pureK f) (pureK f)
    {-# INLINE pureKWith #-}
    pureKWith p f = Pair (pureKWith p f) (pureKWith p f)

instance (KFunctor a, KFunctor b) => KFunctor (Product a b) where
    {-# INLINE mapK #-}
    mapK f (Pair x y) = Pair (mapK f x) (mapK f y)
    {-# INLINE mapKWith #-}
    mapKWith p f (Pair x y) =
        Pair (mapKWith p f x) (mapKWith p f y)

instance (KApply a, KApply b) => KApply (Product a b) where
    {-# INLINE zipK #-}
    zipK (Pair a0 b0) (Pair a1 b1) = Pair (zipK a0 a1) (zipK b0 b1)

{-# INLINE mapK1 #-}
mapK1 ::
    forall k c m n.
    (KFunctor k, NodesConstraint k ((~) c)) =>
    (Tree m c -> Tree n c) ->
    Tree k m ->
    Tree k n
mapK1 = mapKWith (Proxy @((~) c))

{-# INLINE liftK2 #-}
liftK2 ::
    KApply k =>
    (forall c. Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2 f x = mapK (\(Pair a b) -> f a b) . zipK x

{-# INLINE liftK2With #-}
liftK2With ::
    (KApply k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2With p f x = mapKWith p (\(Pair a b) -> f a b) . zipK x
