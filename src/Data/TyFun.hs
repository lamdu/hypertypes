-- | Type-level function representation as data (defunctionalization)
--
-- Extracted from the singletons package to avoid a heavy dependency
{-# LANGUAGE NoImplicitPrelude, TypeOperators #-}
{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies #-}

module Data.TyFun where

import Data.Kind (Type, Constraint)

data TyFun :: Type -> Type -> Type

type a ~> b = TyFun a b -> Type
infixr 0 ~>

type family Apply (f :: i ~> o) (x :: i) :: o

data ConcatConstraintFuncs :: [a ~> Constraint] -> a ~> Constraint
type instance Apply (ConcatConstraintFuncs '[]) c = ()
type instance Apply (ConcatConstraintFuncs (x ': xs)) c =
    ( Apply x c
    , Apply (ConcatConstraintFuncs xs) c
    )
