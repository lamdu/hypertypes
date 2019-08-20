{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module AST.Class.Traversable
    ( KTraversable(..)
    , ContainedK(..), _ContainedK
    , traverseK, traverseKWith, traverseK1
    , sequencePureK, sequencePureKWith
    , sequenceLiftK2, sequenceLiftK2With
    ) where

import AST.Class
import AST.Class.Foldable (KFoldable)
import AST.Knot (Knot, Tree)
import Control.Lens (Iso, iso)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

newtype ContainedK f l (k :: Knot) = MkContainedK { runContainedK :: f (l k) }

{-# INLINE _ContainedK #-}
_ContainedK ::
    Iso (Tree (ContainedK f0 l0) k0)
        (Tree (ContainedK f1 l1) k1)
        (f0 (Tree l0 k0))
        (f1 (Tree l1 k1))
_ContainedK = iso runContainedK MkContainedK

class (KFunctor k, KFoldable k) => KTraversable k where
    sequenceK ::
        Applicative f =>
        Tree k (ContainedK f l) ->
        f (Tree k l)

instance KTraversable (Const a) where
    {-# INLINE sequenceK #-}
    sequenceK (Const x) = pure (Const x)

{-# INLINE traverseK #-}
traverseK ::
    (Applicative f, KTraversable k) =>
    (forall c. Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseK f = sequenceK . mapK (MkContainedK . f)

{-# INLINE traverseKWith #-}
traverseKWith ::
    forall n constraint m f k.
    (Applicative f, KTraversable k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseKWith p f = sequenceK . mapKWith p (MkContainedK . f)

{-# INLINE traverseK1 #-}
traverseK1 ::
    ( Applicative f, KTraversable k
    , NodesConstraint k ((~) c)
    ) =>
    (Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseK1 f = sequenceK . mapK1 (MkContainedK . f)

{-# INLINE sequencePureK #-}
sequencePureK ::
    (Applicative f, KPointed k, KTraversable k) =>
    (forall c. f (Tree n c)) ->
    f (Tree k n)
sequencePureK f = sequenceK (pureK (MkContainedK f))

{-# INLINE sequencePureKWith #-}
sequencePureKWith ::
    (Applicative f, KApplicative k, KTraversable k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => f (Tree n c)) ->
    f (Tree k n)
sequencePureKWith p f = sequenceK (pureKWith p (MkContainedK f))

{-# INLINE sequenceLiftK2 #-}
sequenceLiftK2 ::
    (Applicative f, KApply k, KTraversable k) =>
    (forall c. Tree l c -> Tree m c -> f (Tree n c)) ->
    Tree k l ->
    Tree k m ->
    f (Tree k n)
sequenceLiftK2 f x = sequenceK . liftK2 (\a -> MkContainedK . f a) x

{-# INLINE sequenceLiftK2With #-}
sequenceLiftK2With ::
    (Applicative f, KApply k, KTraversable k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree l c -> Tree m c -> f (Tree n c)) ->
    Tree k l ->
    Tree k m ->
    f (Tree k n)
sequenceLiftK2With p f x = sequenceK . liftK2With p (\a -> MkContainedK . f a) x
