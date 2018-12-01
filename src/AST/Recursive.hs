{-# LANGUAGE NoImplicitPrelude, RankNTypes, ScopedTypeVariables, DefaultSignatures #-}

module AST.Recursive
    ( Recursive(..)
    , hoistNode, hoistBody, hoistNodeR, hoistBodyR
    ) where

import           AST (Node, Children(..), overChildren)
import           Data.Constraint (Dict(..), withDict)
import           Data.Functor.Const (Const(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

class Children expr => Recursive expr where
    recursive :: Proxy expr -> Dict (ChildrenConstraint expr Recursive)

    default recursive ::
        ChildrenConstraint expr Recursive =>
        Proxy expr -> Dict (ChildrenConstraint expr Recursive)
    recursive _ = Dict

hoistNode ::
    (Recursive expr, Functor f) =>
    (forall a. f a -> g a) ->
    Node f expr -> Node g expr
hoistNode f = f . fmap (hoistBody f)

-- | Like `hoistNode` but requiring `Functor` for the second argument
hoistNodeR ::
    (Recursive expr, Functor g) =>
    (forall a. f a -> g a) ->
    Node f expr -> Node g expr
hoistNodeR f = fmap (hoistBodyR f) . f

hoistBody ::
    forall expr f g.
    (Recursive expr, Functor f) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBody f =
    withDict (recursive (Proxy :: Proxy expr))
    (overChildren (Proxy :: Proxy Recursive) (hoistNode f))

hoistBodyR ::
    forall expr f g.
    (Recursive expr, Functor g) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBodyR f =
    withDict (recursive (Proxy :: Proxy expr))
    (overChildren (Proxy :: Proxy Recursive) (hoistNodeR f))

instance Recursive (Const val)
