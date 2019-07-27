{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module AST.Constraint
    ( KnotConstraintFunc(..)
    , KnotsConstraint
    , ConcatKnotConstraints
    , ApplyKnotConstraints
    , KnotConstraint
    ) where

import AST.Knot (Knot)
import Data.Constraint (Constraint, Dict(..), withDict)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

type KnotConstraint = (Knot -> Type) -> Constraint

class KnotConstraintFunc (cls :: KnotConstraint -> Constraint) where
    type family ApplyKnotConstraint cls (c :: KnotConstraint) :: Constraint
    applyKnotConstraint ::
        cls c =>
        Proxy cls ->
        Proxy c ->
        Dict (ApplyKnotConstraint cls c)

-- | Apply a constraint on the given knots
class KnotsConstraint (ks :: [Knot -> Type]) c where
    knotsConstraint ::
        Proxy ks ->
        Proxy c ->
        Dict (ApplyKnotConstraint (KnotsConstraint ks) c)

instance KnotConstraintFunc (KnotsConstraint '[]) where
    type ApplyKnotConstraint (KnotsConstraint '[]) c = ()
    {-# INLINE applyKnotConstraint #-}
    applyKnotConstraint _ = knotsConstraint (Proxy :: Proxy ('[] :: [Knot -> Type]))

instance KnotConstraintFunc (KnotsConstraint (k ': ks)) where
    type ApplyKnotConstraint (KnotsConstraint (k ': ks)) c =
            ( c k
            , ApplyKnotConstraint (KnotsConstraint ks) c
            )
    {-# INLINE applyKnotConstraint #-}
    applyKnotConstraint _ = knotsConstraint (Proxy :: Proxy (k ': ks))

instance KnotsConstraint '[] c where
    {-# INLINE knotsConstraint #-}
    knotsConstraint _ _ = Dict

instance (c k, KnotsConstraint ks c) => KnotsConstraint (k ': ks) c where
    {-# INLINE knotsConstraint #-}
    knotsConstraint _ p =
        withDict (knotsConstraint (Proxy :: Proxy ks) p) Dict

class ConcatKnotConstraints (xs :: [KnotConstraint -> Constraint]) c where
    concatKnotConstraints ::
        Proxy xs ->
        Proxy c ->
        Dict (ApplyKnotConstraint (ConcatKnotConstraints xs) c)

instance KnotConstraintFunc (ConcatKnotConstraints '[]) where
    type ApplyKnotConstraint (ConcatKnotConstraints '[]) c = ()
    {-# INLINE applyKnotConstraint #-}
    applyKnotConstraint _ =
        concatKnotConstraints (Proxy :: Proxy ('[] :: [KnotConstraint -> Constraint]))

instance KnotConstraintFunc (ConcatKnotConstraints (x ': xs)) where
    type ApplyKnotConstraint (ConcatKnotConstraints (x ': xs)) c =
        ( ApplyKnotConstraint x c
        , ApplyKnotConstraint (ConcatKnotConstraints xs) c
        )
    {-# INLINE applyKnotConstraint #-}
    applyKnotConstraint _ = concatKnotConstraints (Proxy :: Proxy (x ': xs))

instance ConcatKnotConstraints '[] c where
    {-# INLINE concatKnotConstraints #-}
    concatKnotConstraints _ _ = Dict

instance
    (KnotConstraintFunc x, x c, ConcatKnotConstraints xs c) =>
    ConcatKnotConstraints (x ': xs) c where

    {-# INLINE concatKnotConstraints #-}
    concatKnotConstraints _ p =
        withDict (applyKnotConstraint (Proxy :: Proxy x) p)
        (withDict (concatKnotConstraints (Proxy :: Proxy xs) p) Dict)

type family ApplyKnotConstraints x cs :: Constraint where
    ApplyKnotConstraints x (c ': cs) = (ApplyKnotConstraint x c, ApplyKnotConstraints x cs)
    ApplyKnotConstraints x '[] = ()
