{-# LANGUAGE NoImplicitPrelude, TypeFamilies, RankNTypes, ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables, DataKinds #-}

module AST.Class.Children
    ( Children(..), ChildrenWithConstraint
    , children_, overChildren, foldMapChildren, foldMapAChildren
    ) where

import AST.Knot (Knot, Tree)
import Control.Lens.Operators
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Proxy (Proxy(..))
import GHC.Exts (Constraint)

import Prelude.Compat

class Children (expr :: Knot -> *) where
    type ChildrenConstraint expr (constraint :: (Knot -> *) -> Constraint) :: Constraint

    children ::
        (Applicative f, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child -> f (Tree m child)) ->
        Tree expr n -> f (Tree expr m)

    leafExpr :: Maybe (expr f -> expr g)
    leafExpr = Nothing

type ChildrenWithConstraint expr constraint = (Children expr, ChildrenConstraint expr constraint)

instance Children (Const val) where
    type ChildrenConstraint (Const val) constraint = ()
    children _ _ (Const x) = pure (Const x)
    leafExpr = Just (\(Const x) -> Const x)

{-# INLINE children_ #-}
children_ ::
    forall f expr constraint n.
    (Applicative f, ChildrenWithConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child -> f ()) ->
    Tree expr n -> f ()
children_ p f e =
    () <$ (children p (\c -> Const () <$ f c) e :: f (Tree expr (Const ())))

{-# INLINE overChildren #-}
overChildren ::
    ChildrenWithConstraint expr constraint =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child -> Tree m child) ->
    Tree expr n -> Tree expr m
overChildren p f = runIdentity . children p (Identity . f)

{-# INLINE foldMapChildren #-}
foldMapChildren ::
    (ChildrenWithConstraint expr constraint, Monoid a) =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child -> a) ->
    Tree expr n -> a
foldMapChildren p f x =
    children_ p (\c -> (f c, ())) x & fst

{-# INLINE foldMapAChildren #-}
foldMapAChildren ::
    forall f expr constraint a n.
    (Applicative f, ChildrenWithConstraint expr constraint, Monoid a) =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child -> f a) ->
    Tree expr n -> f a
foldMapAChildren p f x =
    (children p (\c -> f c <&> Const) x :: f (Tree expr (Const a)))
    <&> foldMapChildren p getConst
