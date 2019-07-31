{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}

module AST.Constraint
    ( ApplyKnotConstraint
    , KnotsConstraint
    , ConcatKnotConstraints
    , KnotConstraint
    ) where

import AST.Knot (Knot)
import Data.Constraint (Constraint)
import Data.Kind (Type)

type KnotConstraint = (Knot -> Type) -> Constraint

type family ApplyKnotConstraint f (c :: KnotConstraint) :: Constraint

-- | Apply a constraint on the given knots
data KnotsConstraint (ks :: [Knot -> Type])
type instance ApplyKnotConstraint (KnotsConstraint '[]) c = ()
type instance ApplyKnotConstraint (KnotsConstraint (k ': ks)) c =
    ( c k
    , ApplyKnotConstraint (KnotsConstraint ks) c
    )

data ConcatKnotConstraints (xs :: [Type])
type instance ApplyKnotConstraint (ConcatKnotConstraints '[]) c = ()
type instance ApplyKnotConstraint (ConcatKnotConstraints (x ': xs)) c =
    ( ApplyKnotConstraint x c
    , ApplyKnotConstraint (ConcatKnotConstraints xs) c
    )
