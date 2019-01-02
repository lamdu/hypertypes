{-# LANGUAGE NoImplicitPrelude, TypeFamilies, RankNTypes, ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables, DataKinds #-}

module AST.Class.Children
    ( Children(..), ChildrenWithConstraint
    , children_, overChildren, foldMapChildren
    ) where

import AST.Knot (Knot, Tree)
import Control.Lens.Operators
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Proxy (Proxy(..))
import GHC.Exts (Constraint)

import Prelude.Compat

class Children (expr :: Knot -> *) where
    type SubTreeConstraint expr (knot :: Knot) (constraint :: * -> Constraint) :: Constraint

    type ChildrenConstraint expr (constraint :: (Knot -> *) -> Constraint) :: Constraint

    children ::
        (Applicative f, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child -> f (Tree m child)) ->
        Tree expr n -> f (Tree expr m)

    childrenNoConstraint ::
        Applicative f =>
        (forall child. Tree n child -> f (Tree m child)) ->
        Tree expr n -> f (Tree expr m)

    leafExpr :: Maybe (expr f -> expr g)
    leafExpr = Nothing

type ChildrenWithConstraint expr constraint = (Children expr, ChildrenConstraint expr constraint)

instance Children (Const val) where
    type SubTreeConstraint (Const val) f constraint = ()
    type ChildrenConstraint (Const val) constraint = ()
    children _ _ (Const x) = pure (Const x)
    childrenNoConstraint _ (Const x) = pure (Const x)
    leafExpr = Just (\(Const x) -> Const x)

children_ ::
    forall f expr constraint n.
    (Applicative f, ChildrenWithConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child -> f ()) ->
    Tree expr n -> f ()
children_ p f e =
    () <$ (children p (\c -> Const () <$ f c) e :: f (Tree expr (Const ())))

overChildren ::
    ChildrenWithConstraint expr constraint =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child -> Tree m child) ->
    Tree expr n -> Tree expr m
overChildren p f = runIdentity . children p (Identity . f)

foldMapChildren ::
    (ChildrenWithConstraint expr constraint, Monoid a) =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child -> a) ->
    Tree expr n -> a
foldMapChildren p f x =
    children_ p (\c -> (f c, ())) x & fst
