{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module AST.Class.Traversable
    ( KTraversable(..)
    , ContainedK(..), _ContainedK
    , traverseK, traverseK1, traverseKWith, traverseKWithDict
    ) where

import AST.Class (KNodes(..), KFunctor(..), MapK(..), mapK, NodeTypesOf)
import AST.Class.Combinators
import AST.Class.Foldable (KFoldable)
import AST.Combinator.ANode (ANode(..))
import AST.Knot (Knot, Tree)
import AST.Knot.Dict (KDict, pureKWithDict)
import Control.Lens (Iso, iso)
import Data.Constraint (withDict)
import Data.Constraint.List (ApplyConstraints)
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
    sequenceC ::
        Applicative f =>
        Tree k (ContainedK f l) ->
        f (Tree k l)

instance KTraversable (Const a) where
    {-# INLINE sequenceC #-}
    sequenceC (Const x) = pure (Const x)

{-# INLINE traverseK #-}
traverseK ::
    (Applicative f, KTraversable k) =>
    (forall c. Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseK f = sequenceC . mapK (MkContainedK . f)

{-# INLINE traverseK1 #-}
traverseK1 ::
    ( Applicative f, KTraversable k
    , NodeTypesOf k ~ ANode c
    ) =>
    (Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseK1 f = sequenceC . mapC (MkSingle (MkMapK (MkContainedK . f)))

{-# INLINE traverseKWith #-}
traverseKWith ::
    forall n constraints m f k.
    (Applicative f, KTraversable k, KLiftConstraints k constraints) =>
    Proxy constraints ->
    (forall c. ApplyConstraints constraints c => Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseKWith p f =
    withDict (kNodes (Proxy :: Proxy k)) $
    withDict (kLiftConstraintsNodeTypes (Proxy :: Proxy k) p) $
    sequenceC . mapC (pureKWith p (MkMapK (MkContainedK . f)))

{-# INLINE traverseKWithDict #-}
traverseKWithDict ::
    forall n constraints m f k.
    (Applicative f, KTraversable k) =>
    Tree (NodeTypesOf k) (KDict constraints) ->
    (forall c. ApplyConstraints constraints c => Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseKWithDict d f =
    withDict (kNodes (Proxy :: Proxy k)) $
    sequenceC . mapC (pureKWithDict d (MkMapK (MkContainedK . f)))
