{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}

module AST.Constraint
    ( Apply
    , KnotsConstraint
    , ConcatKnotConstraints
    , KnotConstraint
    ) where

import AST.Knot (Knot)
import Data.Constraint (Constraint)
import Data.Kind (Type)

type KnotConstraint = (Knot -> Type) -> Constraint

type family Apply f (c :: KnotConstraint) :: Constraint

-- | Apply a constraint on the given knots
data KnotsConstraint (ks :: [Knot -> Type])
type instance Apply (KnotsConstraint '[]) c = ()
type instance Apply (KnotsConstraint (k ': ks)) c =
    ( c k
    , Apply (KnotsConstraint ks) c
    )

data ConcatKnotConstraints (xs :: [Type])
type instance Apply (ConcatKnotConstraints '[]) c = ()
type instance Apply (ConcatKnotConstraints (x ': xs)) c =
    ( Apply x c
    , Apply (ConcatKnotConstraints xs) c
    )
