-- | Type-level function representation as data (defunctionalization)
--
-- TyFun and Apply were extracted from the singletons package to avoid a heavy dependency,
-- and other type-level functions were added.
{-# LANGUAGE NoImplicitPrelude, TypeOperators #-}
{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies #-}

module Data.TyFun where

import Data.Kind (Type, Constraint)

data TyFun :: Type -> Type -> Type

type a ~> b = TyFun a b -> Type
infixr 0 ~>

type family Apply (f :: i ~> o) (x :: i) :: o

data TConst :: r -> a ~> r
type instance Apply (TConst x) y = x

data On :: a -> (a -> r) ~> r
type instance Apply (On x) f = f x

data ConcatConstraintFuncs :: [a ~> Constraint] -> a ~> Constraint
type instance Apply (ConcatConstraintFuncs '[]) c = ()
type instance Apply (ConcatConstraintFuncs (x ': xs)) c =
    ( Apply x c
    , Apply (ConcatConstraintFuncs xs) c
    )
