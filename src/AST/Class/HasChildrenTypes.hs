{-# LANGUAGE NoImplicitPrelude, ConstraintKinds, TypeFamilies, RankNTypes #-}
{-# LANGUAGE FlexibleContexts, DefaultSignatures #-}

module AST.Class.HasChildrenTypes
    ( HasChildrenTypes(..), ChildrenTypesConstraints
    , mapK, liftK2, foldMapK, traverseK, traverseK_
    ) where

import AST.Class.Applicative (KApplicative)
import AST.Class.Apply (KApply(..))
import AST.Class.Foldable (KFoldable(..), ConvertK(..))
import AST.Class.Functor (KFunctor(..), MapK(..))
import AST.Class.Pointed (KPointed(..))
import AST.Class.Traversable (KTraversable(..), ContainedK(..))
import AST.Combinator.Both (Both(..))
import AST.Knot (Tree, ChildrenTypesOf)
import Data.Constraint (Dict(..), withDict)
import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

type ChildrenTypesConstraints k =
    ( ChildrenTypesOf k ~ k
    , HasChildrenTypes k
    , KApplicative k
    )

class HasChildrenTypes k where
    hasChildrenTypes ::
        Proxy k ->
        Dict (ChildrenTypesConstraints (ChildrenTypesOf k))
    {-# INLINE hasChildrenTypes #-}
    default hasChildrenTypes ::
        ChildrenTypesConstraints (ChildrenTypesOf k) =>
        Proxy k ->
        Dict (ChildrenTypesConstraints (ChildrenTypesOf k))
    hasChildrenTypes _ = Dict

    mNoChildren :: Maybe (k m -> k n)
    {-# INLINE mNoChildren #-}
    mNoChildren = Nothing

instance HasChildrenTypes (Const a) where
    {-# INLINE mNoChildren #-}
    mNoChildren = Just (\(Const x) -> Const x)

{-# INLINE withChildrenTypes #-}
withChildrenTypes ::
    HasChildrenTypes k =>
    (ChildrenTypesConstraints (ChildrenTypesOf k) => Tree k l -> a) ->
    Tree k l ->
    a
withChildrenTypes f x =
    withDict (hasChildrenTypes (p x)) (f x)
    where
        p :: Tree k l -> Proxy k
        p _ = Proxy

{-# INLINE mapK #-}
mapK ::
    (KFunctor k, HasChildrenTypes k) =>
    (forall c. Tree m c -> Tree n c) ->
    Tree k m ->
    Tree k n
mapK f = withChildrenTypes (mapC (pureK (MkMapK f)))

{-# INLINE liftK2 #-}
liftK2 ::
    (KApply k, HasChildrenTypes k) =>
    (forall c. Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2 f x = mapK (\(Both a b) -> f a b) . zipK x

{-# INLINE foldMapK #-}
foldMapK ::
    (Monoid a, KFoldable k, HasChildrenTypes k) =>
    (forall c. Tree l c -> a) ->
    Tree k l ->
    a
foldMapK f = withChildrenTypes (foldMapC (pureK (MkConvertK f)))

{-# INLINE traverseK #-}
traverseK ::
    (Applicative f, KTraversable k, HasChildrenTypes k) =>
    (forall c. Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseK f = sequenceC . mapK (MkContainedK . f)

{-# INLINE traverseK_ #-}
traverseK_ ::
    (Applicative f, KFoldable k, HasChildrenTypes k) =>
    (forall c. Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK_ f = sequenceA_ . foldMapK ((:[]) . f)
