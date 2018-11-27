{-# LANGUAGE NoImplicitPrelude, TypeFamilies, RankNTypes, ConstraintKinds, UndecidableInstances, UndecidableSuperClasses, ScopedTypeVariables #-}

module AST
    ( Node, Children(..)
    , overChildren
    , ChildOf, monoChildren
    , leaf, hoist
    ) where

import           Control.Lens (Lens, Traversal)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))
import           GHC.Exts (Constraint)

import           Prelude.Compat

type Node f expr = f (expr f)

class ChildrenConstraint expr Children => Children expr where
    type ChildrenConstraint expr (constraint :: ((* -> *) -> *) -> Constraint) :: Constraint
    children ::
        (Applicative f, Functor n, Functor m, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Node n child -> f (Node m child)) ->
        expr n -> f (expr m)

type family ChildOf (expr :: (* -> *) -> *) :: (* -> *) -> *

monoChildren ::
    forall expr n m.
    ( Children expr, ChildrenConstraint expr ((~) (ChildOf expr))
    , Functor n, Functor m
    ) =>
    Traversal (expr n) (expr m) (Node n (ChildOf expr)) (Node m (ChildOf expr))
monoChildren = children (Proxy :: Proxy ((~) (ChildOf expr)))

overChildren ::
    (ChildrenConstraint expr constraint, Children expr, Functor n, Functor m) =>
    Proxy constraint ->
    (forall child. constraint child => Node n child -> Node m child) ->
    expr n -> expr m
overChildren p f = runIdentity . children p (Identity . f)

instance Children (Const val) where
    type ChildrenConstraint (Const val) constraint = ()
    children _ _ (Const x) = pure (Const x)

leaf ::
    (Functor n, Functor m) =>
    Lens (n a) (m b) (Node n (Const a)) (Node m (Const b))
leaf f x =
    x
    <&> Lens.Const
    & f
    <&> fmap Lens.getConst

hoist ::
    (Children expr, Functor f, Functor g) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoist f = overChildren (Proxy :: Proxy Children) (f . fmap (hoist f))
