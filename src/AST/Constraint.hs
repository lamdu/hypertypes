{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}

module AST.Constraint
    ( KnotConstraintFunc(..)
    , KnotsConstraint
    , ConcatKnotConstraints
    , ApplyKnotConstraints
    , KnotConstraint
    ) where

import AST.Knot (Knot)
import Data.Constraint (Constraint)
import Data.Kind (Type)

type KnotConstraint = (Knot -> Type) -> Constraint

class KnotConstraintFunc (cls :: KnotConstraint -> Constraint) where
    type family ApplyKnotConstraint cls (c :: KnotConstraint) :: Constraint

-- | Apply a constraint on the given knots
class KnotsConstraint (ks :: [Knot -> Type]) (c :: KnotConstraint)

instance KnotConstraintFunc (KnotsConstraint '[]) where
    type ApplyKnotConstraint (KnotsConstraint '[]) c = ()

instance KnotConstraintFunc (KnotsConstraint (k ': ks)) where
    type ApplyKnotConstraint (KnotsConstraint (k ': ks)) c =
            ( c k
            , ApplyKnotConstraint (KnotsConstraint ks) c
            )

instance KnotsConstraint '[] c
instance c k => KnotsConstraint (k ': ks) c

class ConcatKnotConstraints (xs :: [KnotConstraint -> Constraint]) (c :: KnotConstraint)

instance KnotConstraintFunc (ConcatKnotConstraints '[]) where
    type ApplyKnotConstraint (ConcatKnotConstraints '[]) c = ()

instance KnotConstraintFunc (ConcatKnotConstraints (x ': xs)) where
    type ApplyKnotConstraint (ConcatKnotConstraints (x ': xs)) c =
        ( ApplyKnotConstraint x c
        , ApplyKnotConstraint (ConcatKnotConstraints xs) c
        )

instance ConcatKnotConstraints '[] c
instance ConcatKnotConstraints (x ': xs) c

type family ApplyKnotConstraints x cs :: Constraint where
    ApplyKnotConstraints x (c ': cs) = (ApplyKnotConstraint x c, ApplyKnotConstraints x cs)
    ApplyKnotConstraints x '[] = ()
