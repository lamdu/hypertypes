{-# LANGUAGE NoImplicitPrelude, RankNTypes, ScopedTypeVariables, DefaultSignatures, KindSignatures, TypeOperators, ConstraintKinds #-}

module AST.Recursive
    ( Recursive(..)
    , ChildrenRecursive(..), proxyChildrenRecursive, overChildrenRecursive
    , fold, unfold
    , hoistNode, hoistNodeR, hoistBody, hoistBodyR
    ) where

import           AST (Node, Children(..), ChildrenWithConstraint, overChildren)
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

class Recursive (constraint :: ((* -> *) -> *) -> Constraint) where
    recursive ::
        Proxy constraint ->
        Proxy expr ->
        constraint expr :- ChildrenWithConstraint expr constraint

class Children expr => ChildrenRecursive expr where
    childrenRecursive ::
        Proxy expr ->
        Dict (ChildrenWithConstraint expr ChildrenRecursive)
    default childrenRecursive ::
        ChildrenWithConstraint expr ChildrenRecursive =>
        Proxy expr ->
        Dict (ChildrenWithConstraint expr ChildrenRecursive)
    childrenRecursive _ = Dict

instance Recursive ChildrenRecursive where
    recursive _ p = Sub (childrenRecursive p)

proxyChildrenRecursive :: Proxy ChildrenRecursive
proxyChildrenRecursive = Proxy

instance ChildrenRecursive (Const a)

-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
fold ::
    forall constraint expr f.
    (Recursive constraint, constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => child f -> Node f child) ->
    Node Identity expr ->
    Node f expr
fold p f (Identity x) =
    f (overChildren p (fold p f) x)
    \\ recursive p (Proxy :: Proxy expr)

-- | Build/load a tree from a seed value.
-- TODO: Is this a "monadic ana-morphism"?
unfold ::
    forall constraint expr f m.
    (Monad m, Recursive constraint, constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Node f child -> m (child f)) ->
    Node f expr ->
    m (Node Identity expr)
unfold p f x =
    f x >>= children p (unfold p f) <&> Identity
    \\ recursive p (Proxy :: Proxy expr)

overChildrenRecursive ::
    forall expr f g.
    ChildrenRecursive expr =>
    (forall child. ChildrenRecursive child => Node f child -> Node g child) ->
    expr f -> expr g
overChildrenRecursive f =
    overChildren proxyChildrenRecursive f
    \\ recursive proxyChildrenRecursive (Proxy :: Proxy expr)

hoistNode ::
    (ChildrenRecursive expr, Functor f) =>
    (forall a. f a -> g a) ->
    Node f expr -> Node g expr
hoistNode f = f . fmap (hoistBody f)

-- | Like `hoistNode` but requiring `Functor` for the second argument
hoistNodeR ::
    (ChildrenRecursive expr, Functor g) =>
    (forall a. f a -> g a) ->
    Node f expr -> Node g expr
hoistNodeR f = fmap (hoistBodyR f) . f

hoistBody ::
    forall expr f g.
    (ChildrenRecursive expr, Functor f) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBody f = overChildrenRecursive (hoistNode f)

hoistBodyR ::
    forall expr f g.
    (ChildrenRecursive expr, Functor g) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBodyR f = overChildrenRecursive (hoistNodeR f)
