{-# LANGUAGE NoImplicitPrelude, ConstraintKinds, TypeFamilies, RankNTypes #-}
{-# LANGUAGE FlexibleContexts, DefaultSignatures #-}

module AST.Class.HasNodeTypes
    ( HasNodeTypes(..), NodeTypesConstraints
    , mapK, liftK2, foldMapK, traverseK, traverseK1, traverseK_
    ) where

import AST.Class (KPointed(..), KFunctor(..), MapK(..), KApply(..), KApplicative)
import AST.Class.Foldable (KFoldable(..), ConvertK(..))
import AST.Class.Traversable (KTraversable(..), ContainedK(..))
import AST.Combinator.Both (Both(..))
import AST.Combinator.Single
import AST.Knot (Tree, NodeTypesOf)
import Data.Constraint (Dict(..), withDict)
import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

type NodeTypesConstraints k =
    ( NodeTypesOf k ~ k
    , HasNodeTypes k
    , KApplicative k
    )

class HasNodeTypes k where
    hasNodeTypes ::
        Proxy k ->
        Dict (NodeTypesConstraints (NodeTypesOf k))
    {-# INLINE hasNodeTypes #-}
    default hasNodeTypes ::
        NodeTypesConstraints (NodeTypesOf k) =>
        Proxy k ->
        Dict (NodeTypesConstraints (NodeTypesOf k))
    hasNodeTypes _ = Dict

    -- TODO: Remove this.
    -- Algorithms that avoid actions for leafs can more accurately
    -- use KTraversable to check for their presence
    mNoChildren :: Maybe (k m -> k n)
    {-# INLINE mNoChildren #-}
    mNoChildren = Nothing

instance HasNodeTypes (Const a) where
    {-# INLINE mNoChildren #-}
    mNoChildren = Just (\(Const x) -> Const x)

instance HasNodeTypes (Single c)

instance
    (HasNodeTypes a, HasNodeTypes b) =>
    HasNodeTypes (Both a b) where

    {-# INLINE hasNodeTypes #-}
    hasNodeTypes p =
        withDict (hasNodeTypes (pa p)) $
        withDict (hasNodeTypes (pb p)) Dict
        where
            pa :: Proxy (Both a b) -> Proxy a
            pa _ = Proxy
            pb :: Proxy (Both a b) -> Proxy b
            pb _ = Proxy

{-# INLINE withNodeTypes #-}
withNodeTypes ::
    HasNodeTypes k =>
    (NodeTypesConstraints (NodeTypesOf k) => Tree k l -> a) ->
    Tree k l ->
    a
withNodeTypes f x =
    withDict (hasNodeTypes (p x)) (f x)
    where
        p :: Tree k l -> Proxy k
        p _ = Proxy

{-# INLINE mapK #-}
mapK ::
    (KFunctor k, HasNodeTypes k) =>
    (forall c. Tree m c -> Tree n c) ->
    Tree k m ->
    Tree k n
mapK f = withNodeTypes (mapC (pureK (MkMapK f)))

{-# INLINE liftK2 #-}
liftK2 ::
    (KApply k, HasNodeTypes k) =>
    (forall c. Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2 f x = mapK (\(Both a b) -> f a b) . zipK x

{-# INLINE foldMapK #-}
foldMapK ::
    (Monoid a, KFoldable k, HasNodeTypes k) =>
    (forall c. Tree l c -> a) ->
    Tree k l ->
    a
foldMapK f = withNodeTypes (foldMapC (pureK (MkConvertK f)))

{-# INLINE traverseK #-}
traverseK ::
    (Applicative f, KTraversable k, HasNodeTypes k) =>
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

{-# INLINE traverseK_ #-}
traverseK_ ::
    (Applicative f, KFoldable k, HasNodeTypes k) =>
    (forall c. Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK_ f = sequenceA_ . foldMapK ((:[]) . f)
