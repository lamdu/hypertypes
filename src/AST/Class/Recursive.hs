{-# LANGUAGE NoImplicitPrelude, RankNTypes, DefaultSignatures, MultiParamTypeClasses, ConstraintKinds, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

module AST.Class.Recursive
    ( Recursive(..), RecursiveConstraint
    , wrap, unwrap, fold, unfold, foldMapRecursive
    , hoistNode, hoistNodeR, hoistBody, hoistBodyR
    ) where

import           AST.Class.Children (Children(..), overChildren, foldMapChildren)
import           AST.Node (Node)
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

class Children expr => Recursive constraint expr where
    recursive :: Dict (RecursiveConstraint expr constraint)
    default recursive ::
        RecursiveConstraint expr constraint =>
        Dict (RecursiveConstraint expr constraint)
    recursive = Dict

type RecursiveConstraint expr constraint =
    ( constraint expr
    , ChildrenConstraint expr (Recursive constraint)
    )

instance constraint (Const a) => Recursive constraint (Const a)

wrap ::
    forall constraint expr f m.
    (Monad m, Recursive constraint expr) =>
    Proxy constraint ->
    (forall child. Recursive constraint child => child f -> m (Node f child)) ->
    Node Identity expr ->
    m (Node f expr)
wrap p f (Identity x) =
    withDict (recursive :: Dict (RecursiveConstraint expr constraint)) $
    children (Proxy :: Proxy (Recursive constraint)) (wrap p f) x >>= f

unwrap ::
    forall constraint expr f m.
    (Monad m, Recursive constraint expr) =>
    Proxy constraint ->
    (forall child. Recursive constraint child => Node f child -> m (child f)) ->
    Node f expr ->
    m (Node Identity expr)
unwrap p f x =
    withDict (recursive :: Dict (RecursiveConstraint expr constraint)) $
    f x >>= children (Proxy :: Proxy (Recursive constraint)) (unwrap p f) <&> Identity

-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
fold ::
    forall constraint expr a.
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. Recursive constraint child => child (Const a) -> a) ->
    Node Identity expr ->
    a
fold p f = getConst . runIdentity . wrap p (Identity . Const . f)

-- | Build/load a tree from a seed value.
-- TODO: Is this an "ana-morphism"?
unfold ::
    forall constraint expr a.
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. Recursive constraint child => a -> child (Const a)) ->
    a ->
    Node Identity expr
unfold p f = runIdentity . unwrap p (Identity . f . getConst) . Const

foldMapRecursive ::
    forall constraint expr a f.
    (Recursive constraint expr, Monoid a, Foldable f) =>
    Proxy constraint ->
    (forall child. Recursive constraint child => child f -> a) ->
    expr f ->
    a
foldMapRecursive p f x =
    withDict (recursive :: Dict (RecursiveConstraint expr constraint)) $
    f x <>
    foldMapChildren (Proxy :: Proxy (Recursive constraint))
    (foldMap (foldMapRecursive p f)) x

overChildrenRecursive ::
    forall expr f g.
    Recursive Children expr =>
    (forall child. Recursive Children child => Node f child -> Node g child) ->
    expr f -> expr g
overChildrenRecursive f =
    withDict (recursive :: Dict (RecursiveConstraint expr Children)) $
    overChildren (Proxy :: Proxy (Recursive Children)) f

hoistNode ::
    (Recursive Children expr, Functor f) =>
    (forall a. f a -> g a) ->
    Node f expr -> Node g expr
hoistNode f = f . fmap (hoistBody f)

-- | Like `hoistNode` but requiring `Functor` for the second argument
hoistNodeR ::
    (Recursive Children expr, Functor g) =>
    (forall a. f a -> g a) ->
    Node f expr -> Node g expr
hoistNodeR f = fmap (hoistBodyR f) . f

hoistBody ::
    forall expr f g.
    (Recursive Children expr, Functor f) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBody f = overChildrenRecursive (hoistNode f)

hoistBodyR ::
    forall expr f g.
    (Recursive Children expr, Functor g) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBodyR f = overChildrenRecursive (hoistNodeR f)
