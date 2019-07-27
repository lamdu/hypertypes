{-# LANGUAGE NoImplicitPrelude, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances, TypeOperators, TypeFamilies, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Combinators for partially applied constraints on knots

module AST.Class.Combinators
    ( And
    , ApplyKConstraints
    , KLiftConstraints(..)
    , KDict(..), _KDict
    , pureKWith, pureKWithDict
    , mapKWith
    , liftK2With
    ) where

import AST.Class
import AST.Constraint (ApplyKnotConstraint)
import AST.Combinator.Both (Both(..))
import AST.Knot (Tree, Knot, RunKnot)
import Control.Lens (Iso, iso)
import Data.Constraint (Dict(..), Constraint, withDict)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class    (c0 k, c1 k) => And c0 c1 (k :: Knot -> *)
instance (c0 k, c1 k) => And c0 c1 k

type family ApplyKConstraints (k :: Knot -> Type) cs :: Constraint where
    ApplyKConstraints k (c ': cs) = (c k, ApplyKConstraints k cs)
    ApplyKConstraints k '[] = ()

newtype KDict cs k = MkKDict { getKDict :: Dict (ApplyKConstraints (RunKnot k) cs) }

_KDict ::
    Iso (Tree (KDict cs0) k0)
        (Tree (KDict cs1) k1)
        (Dict (ApplyKConstraints k0 cs0))
        (Dict (ApplyKConstraints k1 cs1))
_KDict = iso getKDict MkKDict

class
    HasNodes k =>
    KLiftConstraints k (cs :: [(Knot -> Type) -> Constraint]) where

    kLiftConstraints :: KApplicative k => Tree k (KDict cs)

    kLiftConstraintsNodeTypes ::
        Proxy k -> Proxy cs ->
        Dict (KLiftConstraints (NodeTypesOf k) cs)

instance
    HasNodes k =>
    KLiftConstraints k '[] where

    {-# INLINE kLiftConstraints #-}
    kLiftConstraints = pureK (MkKDict Dict)

    {-# INLINE kLiftConstraintsNodeTypes #-}
    kLiftConstraintsNodeTypes p _ = withDict (hasNodes p) Dict

instance
    ( ApplyKnotConstraint (NodesConstraint k) c
    , KLiftConstraints k cs
    ) =>
    KLiftConstraints k (c ': cs) where

    {-# INLINE kLiftConstraints #-}
    kLiftConstraints =
        liftK2
        (\(MkKDict c) (MkKDict cs) -> withDict c (withDict cs (MkKDict Dict)))
        (pureKWithConstraint (Proxy :: Proxy c) (MkKDict Dict) :: Tree k (KDict '[c]))
        (kLiftConstraints :: Tree k (KDict cs))

    {-# INLINE kLiftConstraintsNodeTypes #-}
    kLiftConstraintsNodeTypes pk _ =
        withDict (hasNodes pk) $
        withDict (kLiftConstraintsNodeTypes pk (Proxy :: Proxy cs))
        Dict

{-# INLINE pureKWith #-}
pureKWith ::
    forall n constraints k.
    (KApplicative k, KLiftConstraints k constraints) =>
    Proxy constraints ->
    (forall child. ApplyKConstraints child constraints => Tree n child) ->
    Tree k n
pureKWith _ = pureKWithDict (kLiftConstraints :: Tree k (KDict constraints))

{-# INLINE pureKWithDict #-}
pureKWithDict ::
    forall n constraints k.
    KFunctor k =>
    Tree k (KDict constraints) ->
    (forall child. ApplyKConstraints child constraints => Tree n child) ->
    Tree k n
pureKWithDict c f = mapK (\(MkKDict d) -> withDict d f) c

{-# INLINE mapKWith #-}
mapKWith ::
    forall k m n constraints.
    (KFunctor k, KLiftConstraints k constraints) =>
    Proxy constraints ->
    (forall child. ApplyKConstraints child constraints => Tree m child -> Tree n child) ->
    Tree k m ->
    Tree k n
mapKWith p f =
    withDict (hasNodes (Proxy :: Proxy k)) $
    withDict (kLiftConstraintsNodeTypes (Proxy :: Proxy k) p) $
    mapC (pureKWith p (MkMapK f))

{-# INLINE liftK2With #-}
liftK2With ::
    (KApply k, KLiftConstraints k constraints) =>
    Proxy constraints ->
    (forall c. ApplyKConstraints c constraints => Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2With p f x = mapKWith p (\(Both a b) -> f a b) . zipK x
