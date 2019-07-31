-- | Type-level function representation as data (defunctionalization)
--
-- `TyFun` and `Apply` were extracted from the `singletons` package to avoid a heavy dependency,
-- And other useful type-level functions were added.
{-# LANGUAGE NoImplicitPrelude, TypeOperators #-}
{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies #-}

module Data.TyFun where

import Data.Kind (Type, Constraint)

-- | Representation of the kind of a type-level function.
-- (see
-- [`singletons`](http://hackage.haskell.org/package/singletons-2.5.1/docs/Data-Singletons.html#t:TyFun)
-- for further explanations)
data TyFun :: Type -> Type -> Type

-- | `a ~> b` is a defunctionalized type function from `a` to `b`
type a ~> b = TyFun a b -> Type
infixr 0 ~>

-- | Type level function application of defunctionalized type functions
type family Apply (f :: i ~> o) (x :: i) :: o

-- | Type level `const` function
data TConst :: r -> a ~> r
type instance Apply (TConst x) y = x

-- | Type level `on x f = f x`
data On :: a -> (a -> r) ~> r
type instance Apply (On x) f = f x

-- | Type level `foldMap . on` for `Constraint`s
data ConcatConstraintFuncs :: [a ~> Constraint] -> a ~> Constraint
type instance Apply (ConcatConstraintFuncs '[]) c = ()
type instance Apply (ConcatConstraintFuncs (x ': xs)) c =
    ( Apply x c
    , Apply (ConcatConstraintFuncs xs) c
    )
