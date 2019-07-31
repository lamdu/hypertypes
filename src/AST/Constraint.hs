{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}

module AST.Constraint
    ( ApplyKnotConstraint
    , KnotsConstraint
    , ConcatKnotConstraints
    , ApplyKnotConstraints
    , KnotConstraint
    ) where

import AST.Knot (Knot)
import Data.Constraint (Constraint)
import Data.Kind (Type)

type KnotConstraint = (Knot -> Type) -> Constraint

type family ApplyKnotConstraint (cls :: Constraint) (c :: KnotConstraint) :: Constraint
type instance ApplyKnotConstraint (KnotsConstraint '[]) c = ()
type instance ApplyKnotConstraint (KnotsConstraint (k ': ks)) c =
    ( c k
    , ApplyKnotConstraint (KnotsConstraint ks) c
    )

-- | Apply a constraint on the given knots
class KnotsConstraint (ks :: [Knot -> Type])

class ConcatKnotConstraints (xs :: [Constraint])

type instance ApplyKnotConstraint (ConcatKnotConstraints '[]) c = ()
type instance ApplyKnotConstraint (ConcatKnotConstraints (x ': xs)) c =
    ( ApplyKnotConstraint x c
    , ApplyKnotConstraint (ConcatKnotConstraints xs) c
    )

type family ApplyKnotConstraints x cs :: Constraint where
    ApplyKnotConstraints x (c ': cs) = (ApplyKnotConstraint x c, ApplyKnotConstraints x cs)
    ApplyKnotConstraints x '[] = ()
