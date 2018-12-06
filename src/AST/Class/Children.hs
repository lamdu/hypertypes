{-# LANGUAGE NoImplicitPrelude, TypeFamilies, RankNTypes, ConstraintKinds #-}

module AST.Class.Children
    ( Children(..), ChildrenWithConstraint
    , overChildren
    , IfChildNodes
    ) where

import           AST.Node
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))
import           GHC.Exts (Constraint)

import           Prelude.Compat

class Children expr where
    type ChildrenConstraint expr (constraint :: ((* -> *) -> *) -> Constraint) :: Constraint
    children ::
        (Applicative f, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Node n child -> f (Node m child)) ->
        expr n -> f (expr m)

type ChildrenWithConstraint expr constraint = (Children expr, ChildrenConstraint expr constraint)

instance Children (Const val) where
    type ChildrenConstraint (Const val) constraint = ()
    children _ _ (Const x) = pure (Const x)

overChildren ::
    ChildrenWithConstraint expr constraint =>
    Proxy constraint ->
    (forall child. constraint child => Node n child -> Node m child) ->
    expr n -> expr m
overChildren p f = runIdentity . children p (Identity . f)

-- | Used for standalone deriving clauses like
-- `deriving instance IfChildNodes Typ f Eq => Eq (Typ f)`
type IfChildNodes expr f constraint = ChildrenConstraint expr (NodeConstraint constraint f)
