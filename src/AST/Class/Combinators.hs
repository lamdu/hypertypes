{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, UndecidableInstances, RankNTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Combinators for partially applied constraints on knots

module AST.Class.Combinators
    ( KLiftConstraints(..), KLiftConstraint
    , pureKWith
    , mapKWith
    , liftK2With
    ) where

import AST.Class
import AST.Knot (Tree, Knot)
import AST.Knot.Dict (KDict(..), pureKWithDict)
import Data.Constraint (Dict(..), Constraint, withDict)
import Data.Constraint.List (ApplyConstraints)
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Kind (Type)
import Data.Proxy (Proxy(..))
import Data.TyFun

import Prelude.Compat

class    NodesConstraint k $ c => KLiftConstraint c k
instance NodesConstraint k $ c => KLiftConstraint c k

class
    KNodes k =>
    KLiftConstraints (cs :: [(Knot -> Type) -> Constraint]) k where

    kLiftConstraints :: KApplicative k => Tree k (KDict cs)

    kLiftConstraintsNodeTypes ::
        Proxy k -> Proxy cs ->
        Dict (KLiftConstraints cs (NodeTypesOf k))

instance
    KNodes k =>
    KLiftConstraints '[] k where

    {-# INLINE kLiftConstraints #-}
    kLiftConstraints = pureK (MkKDict Dict)

    {-# INLINE kLiftConstraintsNodeTypes #-}
    kLiftConstraintsNodeTypes p _ = withDict (kNodes p) Dict

instance
    ( KLiftConstraint c k
    , KLiftConstraints cs k
    ) =>
    KLiftConstraints (c ': cs) k where

    {-# INLINE kLiftConstraints #-}
    kLiftConstraints =
        liftK2
        (\(MkKDict c) (MkKDict cs) -> withDict c (withDict cs (MkKDict Dict)))
        (pureKWithConstraint (Proxy @c) (MkKDict Dict) :: Tree k (KDict '[c]))
        (kLiftConstraints :: Tree k (KDict cs))

    {-# INLINE kLiftConstraintsNodeTypes #-}
    kLiftConstraintsNodeTypes pk _ =
        withDict (kNodes pk) $
        withDict (kLiftConstraintsNodeTypes pk (Proxy @cs))
        Dict

{-# INLINE pureKWith #-}
pureKWith ::
    forall n constraints k.
    (KApplicative k, KLiftConstraints constraints k) =>
    Proxy constraints ->
    (forall child. ApplyConstraints constraints child => Tree n child) ->
    Tree k n
pureKWith _ = pureKWithDict (kLiftConstraints :: Tree k (KDict constraints))

{-# INLINE mapKWith #-}
mapKWith ::
    forall k m n constraints.
    (KFunctor k, KLiftConstraints constraints k) =>
    Proxy constraints ->
    (forall child. ApplyConstraints constraints child => Tree m child -> Tree n child) ->
    Tree k m ->
    Tree k n
mapKWith p f =
    withDict (kNodes (Proxy @k)) $
    withDict (kLiftConstraintsNodeTypes (Proxy @k) p) $
    mapC (pureKWith p (MkMapK f))

{-# INLINE liftK2With #-}
liftK2With ::
    (KApply k, KLiftConstraints constraints k) =>
    Proxy constraints ->
    (forall c. ApplyConstraints constraints c => Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2With p f x = mapKWith p (\(Pair a b) -> f a b) . zipK x
