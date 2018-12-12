{-# LANGUAGE NoImplicitPrelude, RankNTypes, ScopedTypeVariables, DefaultSignatures, KindSignatures, TypeOperators, ConstraintKinds #-}

module AST.Class.Recursive
    ( Recursive(..)
    , ChildrenRecursive(..), proxyChildrenRecursive, overChildrenRecursive
    , wrap, unwrap, fold, unfold, foldMapRecursive
    , hoistNode, hoistNodeR, hoistBody, hoistBodyR
    ) where

import           AST.Class.Children (Children(..), ChildrenWithConstraint, overChildren, foldMapChildren)
import           AST.Node (Node)
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

class Recursive (cls :: ((* -> *) -> *) -> Constraint) where
    recursive ::
        Proxy cls ->
        Proxy expr ->
        cls expr :- ChildrenWithConstraint expr cls

class Children expr => ChildrenRecursive expr where
    childrenRecursive ::
        Dict (ChildrenWithConstraint expr ChildrenRecursive)
    default childrenRecursive ::
        ChildrenWithConstraint expr ChildrenRecursive =>
        Dict (ChildrenWithConstraint expr ChildrenRecursive)
    childrenRecursive = Dict

instance Recursive ChildrenRecursive where
    recursive _ _ = Sub childrenRecursive

proxyChildrenRecursive :: Proxy ChildrenRecursive
proxyChildrenRecursive = Proxy

instance ChildrenRecursive (Const a)

wrap ::
    forall constraint expr f m.
    (Monad m, Recursive constraint, constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => child f -> m (Node f child)) ->
    Node Identity expr ->
    m (Node f expr)
wrap p f (Identity x) =
    children p (wrap p f) x >>= f
    \\ recursive p (Proxy :: Proxy expr)

unwrap ::
    forall constraint expr f m.
    (Monad m, Recursive constraint, constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Node f child -> m (child f)) ->
    Node f expr ->
    m (Node Identity expr)
unwrap p f x =
    f x >>= children p (unwrap p f) <&> Identity
    \\ recursive p (Proxy :: Proxy expr)


-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
fold ::
    forall constraint expr a.
    (Recursive constraint, constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => child (Const a) -> a) ->
    Node Identity expr ->
    a
fold p f = getConst . runIdentity . wrap p (Identity . Const . f)

-- | Build/load a tree from a seed value.
-- TODO: Is this a "monadic ana-morphism"?
unfold ::
    forall constraint expr a.
    (Recursive constraint, constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => a -> child (Const a)) ->
    a ->
    Node Identity expr
unfold p f = runIdentity . unwrap p (Identity . f . getConst) . Const

foldMapRecursive ::
    forall constraint expr a f.
    ( Recursive constraint, constraint expr
    , Monoid a, Foldable f
    ) =>
    Proxy constraint ->
    (forall child. constraint child => child f -> a) ->
    expr f ->
    a
foldMapRecursive p f x =
    f x <> foldMapChildren p (foldMap (foldMapRecursive p f)) x
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
