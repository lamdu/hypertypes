{-# LANGUAGE NoImplicitPrelude, RankNTypes, ScopedTypeVariables, DefaultSignatures, KindSignatures, TypeOperators, ConstraintKinds #-}

module AST.Recursive
    ( Recursive(..)
    , ChildrenRecursive(..), proxyChildrenRecursive
    , fold
    , hoistNode, hoistNodeR, hoistBody, hoistBodyR
    ) where

import           AST (Node, Children(..), ChildrenWithConstraint, overChildren)
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

fold ::
    forall constraint expr f.
    (Recursive constraint, constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => child f -> Node f child) ->
    expr Identity ->
    Node f expr
fold p f x =
    f (overChildren p (fold p f . runIdentity) x)
    \\ recursive p (Proxy :: Proxy expr)

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
hoistBody f =
    overChildren proxyChildrenRecursive (hoistNode f)
    \\ recursive proxyChildrenRecursive (Proxy :: Proxy expr)

hoistBodyR ::
    forall expr f g.
    (ChildrenRecursive expr, Functor g) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBodyR f =
    overChildren proxyChildrenRecursive (hoistNodeR f)
    \\ recursive proxyChildrenRecursive (Proxy :: Proxy expr)
