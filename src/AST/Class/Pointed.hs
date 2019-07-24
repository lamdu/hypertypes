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

    -- | Lift a constraint to apply to each of a knot's children types.
    --
    -- Note: It would seem natural to use a simpler type family
    -- which enumerates the children types.
    -- It could be then used to lift a constraint to each of them.
    -- But - making such a family is impossible for knots which have
    -- an unbounded set of children types, such as
    -- `Flip GTerm (LangA Nothing)` (with `LangA` from the test suite).
    type KLiftConstraint k (c :: (Knot -> Type) -> Constraint) :: Constraint

    -- | Construct a value from a higher ranked child value with a constraint
    pureKWithConstraint ::
        KLiftConstraint k constraint =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child) ->
        Tree k n

instance Monoid a => KPointed (Const a) where
    type KLiftConstraint (Const a) c = ()
    {-# INLINE pureC #-}
    pureC _ = Const mempty
    {-# INLINE pureK #-}
    pureK _ = Const mempty
    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint _ _ = Const mempty
