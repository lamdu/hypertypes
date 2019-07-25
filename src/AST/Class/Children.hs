{-# LANGUAGE NoImplicitPrelude, TypeFamilies, RankNTypes, ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

module AST.Class.Children
    ( Children(..)
    ) where

import AST.Knot (Knot, Tree)
import Data.Constraint (Constraint)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

class Children (expr :: Knot -> *) where
    type ChildrenConstraint expr (constraint :: (Knot -> *) -> Constraint) :: Constraint

    children ::
        (Applicative f, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child -> f (Tree m child)) ->
        Tree expr n -> f (Tree expr m)

instance Children (Const val) where
    type ChildrenConstraint (Const val) constraint = ()
    children _ _ (Const x) = pure (Const x)
