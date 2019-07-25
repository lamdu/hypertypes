{-# LANGUAGE NoImplicitPrelude, DataKinds, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances, TypeOperators, TypeFamilies, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications #-}

-- | Combinators for partially applied constraints on knots

module AST.Class.Combinators
    ( And
    , NodeHasConstraint
    , ApplyKConstraints
    , KLiftConstraints(..)
    , pureKWith
    , mapKWith
    , liftK2With
    , foldMapKWith
    , traverseKWith
    , traverseKWith_
    ) where

import AST.Class
import AST.Class.HasNodeTypes
import AST.Class.Foldable
import AST.Class.Traversable
import AST.Combinator.Both
import AST.Knot
import Control.Lens.Operators
import Data.Constraint (Dict(..), Constraint, withDict)
import Data.Foldable (sequenceA_)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class    (c0 k, c1 k) => And c0 c1 (k :: Knot -> *)
instance (c0 k, c1 k) => And c0 c1 k

class    constraint (Node outer k) => NodeHasConstraint constraint outer k
instance constraint (Node outer k) => NodeHasConstraint constraint outer k

type family ApplyKConstraints cs (k :: Knot -> Type) :: Constraint where
    ApplyKConstraints (c ': cs) k = (c k, ApplyKConstraints cs k)
    ApplyKConstraints '[] k = ()

newtype KDict cs k = MkKDict (Dict (ApplyKConstraints cs (RunKnot k)))

class
    (KApplicative k, HasNodeTypes k) =>
    KLiftConstraints (cs :: [(Knot -> Type) -> Constraint]) k where
    kLiftConstraint :: Tree k (KDict cs)

instance
    (KApplicative k, HasNodeTypes k) =>
    KLiftConstraints '[] k where
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint = pureK (MkKDict Dict)

instance
    (KLiftConstraints cs k, KLiftConstraint k c) =>
    KLiftConstraints (c ': cs) k where
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint =
        liftK2
        (\(MkKDict c) (MkKDict cs) -> withDict c (withDict cs (MkKDict Dict)))
        (pureKWithConstraint (Proxy :: Proxy c) (MkKDict Dict) :: Tree k (KDict '[c]))
        (kLiftConstraint :: Tree k (KDict cs))

{-# INLINE pureKWith #-}
pureKWith ::
    forall n constraints k.
    KLiftConstraints constraints k =>
    Proxy constraints ->
    (forall child. ApplyKConstraints constraints child => Tree n child) ->
    Tree k n
pureKWith _ f = mapK (\(MkKDict d) -> withDict d f) (kLiftConstraint :: Tree k (KDict constraints))

{-# INLINE mapKWith #-}
mapKWith ::
    (KFunctor k, KLiftConstraints constraints (NodeTypesOf k)) =>
    Proxy constraints ->
    (forall child. ApplyKConstraints constraints child => Tree m child -> Tree n child) ->
    Tree k m ->
    Tree k n
mapKWith p f = mapC (pureKWith p (MkMapK f))

{-# INLINE liftK2With #-}
liftK2With ::
    (KApply k, KLiftConstraints constraints (NodeTypesOf k)) =>
    Proxy constraints ->
    (forall c. ApplyKConstraints constraints c => Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2With p f x = mapKWith p (\(Both a b) -> f a b) . zipK x

{-# INLINE foldMapKWith #-}
foldMapKWith ::
    (Monoid a, KFoldable k, KLiftConstraints constraints (NodeTypesOf k)) =>
    Proxy constraints ->
    (forall child. ApplyKConstraints constraints child => Tree n child -> a) ->
    Tree k n ->
    a
foldMapKWith p f = foldMapC (pureKWith p (_ConvertK # f))

{-# INLINE traverseKWith #-}
traverseKWith ::
    forall n constraints m f k.
    (Applicative f, KTraversable k, KLiftConstraints constraints (NodeTypesOf k)) =>
    Proxy constraints ->
    (forall c. ApplyKConstraints constraints c => Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseKWith p f = sequenceC . mapC (pureKWith p (MkMapK (MkContainedK . f)))

{-# INLINE traverseKWith_ #-}
traverseKWith_ ::
    forall f k constraints m.
    (Applicative f, KFoldable k, KLiftConstraints constraints (NodeTypesOf k)) =>
    Proxy constraints ->
    (forall c. ApplyKConstraints constraints c => Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseKWith_ p f =
    sequenceA_ . foldMapKWith @[f ()] p ((:[]) . f)
