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

type family ApplyKnotConstraint (cls :: KnotConstraint -> Constraint) (c :: KnotConstraint) :: Constraint
type instance ApplyKnotConstraint (KnotsConstraint '[]) c = ()
type instance ApplyKnotConstraint (KnotsConstraint (k ': ks)) c =
    ( c k
    , ApplyKnotConstraint (KnotsConstraint ks) c
    )

-- | Apply a constraint on the given knots
class KnotsConstraint (ks :: [Knot -> Type]) (c :: KnotConstraint)
instance KnotsConstraint '[] c
instance c k => KnotsConstraint (k ': ks) c

class ConcatKnotConstraints (xs :: [KnotConstraint -> Constraint]) (c :: KnotConstraint)

type instance ApplyKnotConstraint (ConcatKnotConstraints '[]) c = ()
type instance ApplyKnotConstraint (ConcatKnotConstraints (x ': xs)) c =
    ( ApplyKnotConstraint x c
    , ApplyKnotConstraint (ConcatKnotConstraints xs) c
    )

instance ConcatKnotConstraints '[] c
instance ConcatKnotConstraints (x ': xs) c

type family ApplyKnotConstraints x cs :: Constraint where
    ApplyKnotConstraints x (c ': cs) = (ApplyKnotConstraint x c, ApplyKnotConstraints x cs)
    ApplyKnotConstraints x '[] = ()
