{-# LANGUAGE NoImplicitPrelude, RankNTypes, ScopedTypeVariables, DefaultSignatures #-}

module AST.Recursive
    ( Recursive(..)
    , hoistNode, hoistBody
    ) where

import           AST (Node, Children(..), overChildren)
import           Data.Constraint (Dict(..), withDict)
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
hoistNode f =
    f . fmap (hoistBody f)
    -- TODO:
    -- `fmap (hoistBody f) . f` would require `Functor g` instead of `Functor f`
    -- Which one should be available, or both or none?

hoistBody ::
    forall expr f g.
    (Recursive expr, Functor f) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoistBody f =
    withDict (recursive (Proxy :: Proxy expr))
    (overChildren (Proxy :: Proxy Recursive) (hoistNode f))
