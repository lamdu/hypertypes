{-# LANGUAGE NoImplicitPrelude, DefaultSignatures, FlexibleInstances, TypeFamilies, RankNTypes, ConstraintKinds, ScopedTypeVariables #-}

module AST.Class.Children
    ( Children(..), ChildrenWithConstraint
    , EmptyConstraint
    , IfChildNodes
    , children_, overChildren, foldMapChildren
    ) where

import AST.Node
import Control.Lens.Operators
import Data.Constraint
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Proxy (Proxy(..))
import GHC.Exts (Constraint)

import Prelude.Compat

class EmptyConstraint (expr :: (* -> *) -> *)
instance EmptyConstraint expr

class Children expr where
    type ChildrenConstraint expr (constraint :: ((* -> *) -> *) -> Constraint) :: Constraint

    children ::
        (Applicative f, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Node n child -> f (Node m child)) ->
        expr n -> f (expr m)

    childrenEmptyConstraints ::
        Proxy expr -> Dict (ChildrenConstraint expr EmptyConstraint)
    default childrenEmptyConstraints ::
        ChildrenConstraint expr EmptyConstraint =>
        Proxy expr ->
        Dict (ChildrenConstraint expr EmptyConstraint)
    childrenEmptyConstraints _ = Dict

    leafExpr :: Maybe (expr f -> expr g)
    leafExpr = Nothing

type ChildrenWithConstraint expr constraint = (Children expr, ChildrenConstraint expr constraint)

instance Children (Const val) where
    type ChildrenConstraint (Const val) constraint = ()
    children _ _ (Const x) = pure (Const x)
    leafExpr = Just (\(Const x) -> Const x)

-- | Used for standalone deriving clauses like
-- `deriving instance IfChildNodes Typ f Eq => Eq (Typ f)`
type IfChildNodes expr f constraint = ChildrenConstraint expr (NodeConstraint constraint f)

children_ ::
    forall f expr constraint n.
    (Applicative f, ChildrenWithConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Node n child -> f ()) ->
    expr n -> f ()
children_ p f e =
    () <$ (children p (\c -> Const () <$ f c) e :: f (expr (Const ())))

overChildren ::
    ChildrenWithConstraint expr constraint =>
    Proxy constraint ->
    (forall child. constraint child => Node n child -> Node m child) ->
    expr n -> expr m
overChildren p f = runIdentity . children p (Identity . f)

foldMapChildren ::
    (ChildrenWithConstraint expr constraint, Monoid a) =>
    Proxy constraint ->
    (forall child. constraint child => Node n child -> a) ->
    expr n -> a
foldMapChildren p f x =
    children_ p (\c -> (f c, ())) x & fst
