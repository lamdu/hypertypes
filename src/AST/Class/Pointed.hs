{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, RankNTypes #-}
{-# LANGUAGE ConstraintKinds, FlexibleInstances #-}

module AST.Class.Pointed
    ( KPointed(..)
    ) where

import AST.Knot (Knot, Tree, ChildrenTypesOf)
import Data.Constraint (Constraint)
import Data.Functor.Const (Const(..))
import Data.Kind (Type)
import Data.Proxy (Proxy)

import Prelude.Compat

class KPointed k where
    -- | Construct a value from given child values
    pureC ::
        Tree (ChildrenTypesOf k) n ->
        Tree k n

    -- | Construct a value from a higher ranked child value
    pureK ::
        (forall child. Tree n child) ->
        Tree k n

    type KLiftConstraint k (c :: (Knot -> Type) -> Constraint) :: Constraint

    -- | Construct a value from a higher ranked child value with a constraint
    pureKWith ::
        KLiftConstraint k constraint =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child) ->
        Tree k n

instance KPointed (Const ()) where
    type KLiftConstraint (Const ()) c = ()
    pureC = id
    pureK _ = Const ()
    pureKWith _ _ = Const ()
