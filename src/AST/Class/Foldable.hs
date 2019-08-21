{-# LANGUAGE RankNTypes #-}

module AST.Class.Foldable
    ( KFoldable(..)
    , foldMapK1
    , traverseK_, traverseKWith_, traverseK1_
    , sequenceLiftK2_, sequenceLiftK2With_
    ) where

import AST.Class.Apply (KApply, liftK2, liftK2With)
import AST.Class.Nodes (KNodes(..))
import AST.Knot (Tree)
import Data.Constraint (withDict)
import Data.Constraint.List (NoConstraint)
import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

class KNodes k => KFoldable k where
    foldMapK ::
        Monoid a =>
        (forall c. Tree l c -> a) ->
        Tree k l ->
        a
    {-# INLINE foldMapK #-}
    foldMapK f =
        kNoConstraints (Proxy @k) $
        foldMapKWith (Proxy @NoConstraint) f

    foldMapKWith ::
        (Monoid a, NodesConstraint k constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child -> a) ->
        Tree k n ->
        a

instance KFoldable (Const a) where
    {-# INLINE foldMapKWith #-}
    foldMapKWith _ _ _ = mempty

{-# INLINE foldMapK1 #-}
foldMapK1 ::
    forall a k c l.
    ( Monoid a, KFoldable k
    , NodesConstraint k ((~) c)
    ) =>
    (Tree l c -> a) ->
    Tree k l ->
    a
foldMapK1 = foldMapKWith (Proxy @((~) c))

{-# INLINE traverseK_ #-}
traverseK_ ::
    (Applicative f, KFoldable k) =>
    (forall c. Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK_ f = sequenceA_ . foldMapK ((:[]) . f)

{-# INLINE traverseKWith_ #-}
traverseKWith_ ::
    forall f k constraint m.
    (Applicative f, KFoldable k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseKWith_ p f =
    sequenceA_ . foldMapKWith @_ @[f ()] p ((:[]) . f)

{-# INLINE traverseK1_ #-}
traverseK1_ ::
    forall f k c m.
    ( Applicative f, KFoldable k
    , NodesConstraint k ((~) c)
    ) =>
    (Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK1_ = traverseKWith_ (Proxy @((~) c))

{-# INLINE sequenceLiftK2_ #-}
sequenceLiftK2_ ::
    (Applicative f, KApply k, KFoldable k) =>
    (forall c. Tree l c -> Tree m c -> f ()) ->
    Tree k l ->
    Tree k m ->
    f ()
sequenceLiftK2_ f x =
    sequenceA_ . foldMapK ((:[]) . getConst) . liftK2 (\a -> Const . f a) x

{-# INLINE sequenceLiftK2With_ #-}
sequenceLiftK2With_ ::
    forall f k constraint l m.
    (Applicative f, KApply k, KFoldable k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree l c -> Tree m c -> f ()) ->
    Tree k l ->
    Tree k m ->
    f ()
sequenceLiftK2With_ p f x =
    sequenceA_ . foldMapK @_ @[f ()] ((:[]) . getConst) . liftK2With p (\a -> Const . f a) x
