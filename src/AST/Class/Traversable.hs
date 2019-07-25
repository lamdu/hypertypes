{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds, RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module AST.Class.Traversable
    ( KTraversable(..)
    , ContainedK(..), _ContainedK
    , traverseK, traverseK1
    ) where

import AST.Class (KFunctor(..), MapK(..), mapK, HasNodes, NodeTypesOf)
import AST.Class.Foldable (KFoldable)
import AST.Combinator.Single (Single(..))
import AST.Knot (Knot, Tree)
import Control.Lens (Iso, iso)
import Data.Functor.Const (Const(..))

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
    sequenceC ::
        Applicative f =>
        Tree k (ContainedK f l) ->
        f (Tree k l)

instance KTraversable (Const a) where
    {-# INLINE sequenceC #-}
    sequenceC (Const x) = pure (Const x)

{-# INLINE traverseK #-}
traverseK ::
    (Applicative f, KTraversable k, HasNodes k) =>
    (forall c. Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseK f = sequenceC . mapK (MkContainedK . f)

{-# INLINE traverseK1 #-}
traverseK1 ::
    ( Applicative f, KTraversable k
    , NodeTypesOf k ~ (Single c)
    ) =>
    (Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseK1 f = sequenceC . mapC (MkSingle (MkMapK (MkContainedK . f)))
