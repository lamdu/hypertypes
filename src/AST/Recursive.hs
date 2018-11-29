{-# LANGUAGE RankNTypes, ScopedTypeVariables, DefaultSignatures #-}

module AST.Recursive
    ( Recursive(..)
    , hoistNode, hoistBody
    ) where

import AST (Node, Children(..), overChildren)
import Data.Constraint
import Data.Proxy

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

hoistBody ::
    forall expr f g.
    (Recursive expr, Functor f) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBody f =
    withDict (recursive (Proxy :: Proxy expr))
    (overChildren (Proxy :: Proxy Recursive) (hoistNode f))
