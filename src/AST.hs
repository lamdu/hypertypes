{-# LANGUAGE NoImplicitPrelude, TypeFamilies, RankNTypes, ConstraintKinds, ScopedTypeVariables #-}

module AST
    ( Node, LeafNode
    , Children(..), ChildrenWithConstraint
    , ChildOf, monoChildren
    , overChildren
    ) where

import           Control.Lens (Traversal)
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))
import           GHC.Exts (Constraint)

import           Prelude.Compat

type Node f expr = f (expr f)
type LeafNode f expr = Node f (Const expr)

class Children expr where
    type ChildrenConstraint expr (constraint :: ((* -> *) -> *) -> Constraint) :: Constraint
    children ::
        (Applicative f, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Node n child -> f (Node m child)) ->
        expr n -> f (expr m)

type ChildrenWithConstraint expr constraint = (Children expr, ChildrenConstraint expr constraint)

type family ChildOf (expr :: (* -> *) -> *) :: (* -> *) -> *

monoChildren ::
    forall expr n m.
    (ChildrenWithConstraint expr ((~) (ChildOf expr))) =>
    Traversal (expr n) (expr m) (Node n (ChildOf expr)) (Node m (ChildOf expr))
monoChildren = children (Proxy :: Proxy ((~) (ChildOf expr)))

overChildren ::
    ChildrenWithConstraint expr constraint =>
    Proxy constraint ->
    (forall child. constraint child => Node n child -> Node m child) ->
    expr n -> expr m
overChildren p f = runIdentity . children p (Identity . f)

instance Children (Const val) where
    type ChildrenConstraint (Const val) constraint = ()
    children _ _ (Const x) = pure (Const x)
