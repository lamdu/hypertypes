{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TypeOperators #-}
{-# LANGUAGE ConstraintKinds, PolyKinds #-}

module AST.Constraint
    ( KnotsConstraint
    , KnotConstraint
    ) where

import AST.Knot (Knot)
import Data.Constraint (Constraint)
import Data.Kind (Type)
import Data.TyFun

type KnotConstraint = (Knot -> Type) -> Constraint

-- | Apply a constraint on the given knots
data KnotsConstraint :: [Knot -> Type] -> KnotConstraint ~> Constraint
type instance Apply (KnotsConstraint '[]) c = ()
type instance Apply (KnotsConstraint (k ': ks)) c =
    ( c k
    , Apply (KnotsConstraint ks) c
    )
