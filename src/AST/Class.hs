{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, RankNTypes #-}
{-# LANGUAGE ConstraintKinds, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}

module AST.Class
    ( HasNodes(..), NodeTypesConstraints
    , KPointed(..)
    , KFunctor(..), MapK(..), _MapK
    , KApply(..)
    , KApplicative
    , mapK, liftK2
    ) where

import AST.Combinator.Both (Both(..))
import AST.Knot (Knot, Tree)
import Control.Lens (Iso, iso)
import Data.Constraint
import Data.Functor.Const (Const(..))
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

type NodeTypesConstraints k =
    ( NodeTypesOf k ~ k
    , HasNodes k
    , KApplicative k
    )

class HasNodes k where
    -- | A type family for the different types of children a knot has.
    -- Maps to a simple knot which has a single child of each child type.
    type family NodeTypesOf k :: Knot -> Type

    hasNodeTypes ::
        Proxy k ->
        Dict (NodeTypesConstraints (NodeTypesOf k))
    {-# INLINE hasNodeTypes #-}
    default hasNodeTypes ::
        NodeTypesConstraints (NodeTypesOf k) =>
        Proxy k ->
        Dict (NodeTypesConstraints (NodeTypesOf k))
    hasNodeTypes _ = Dict

    -- TODO: Remove this.
    -- Algorithms that avoid actions for leafs can more accurately
    -- use KTraversable to check for their presence
    mNoChildren :: Maybe (k m -> k n)
    {-# INLINE mNoChildren #-}
    mNoChildren = Nothing

class HasNodes k => KPointed k where
    -- | Construct a value from given child values
    pureC ::
        Tree (NodeTypesOf k) n ->
        Tree k n

    -- | Construct a value from a higher ranked child value
    pureK ::
        (forall child. Tree n child) ->
        Tree k n

    -- | Lift a constraint to apply to each of a knot's children types.
    --
    -- Note: It would seem natural to use a simpler type family
    -- which enumerates the children types.
    -- It could be then used to lift a constraint to each of them.
    -- But - making such a family is impossible for knots which have
    -- an unbounded set of children types, such as
    -- `Flip GTerm (LangA Nothing)` (with `LangA` from the test suite).
    type KLiftConstraint k (c :: (Knot -> Type) -> Constraint) :: Constraint
    type KLiftConstraint k c = KLiftConstraint (NodeTypesOf k) c

    -- | Construct a value from a higher ranked child value with a constraint
    pureKWithConstraint ::
        KLiftConstraint k constraint =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child) ->
        Tree k n

newtype MapK m n (k :: Knot) = MkMapK { runMapK :: m k -> n k }

{-# INLINE _MapK #-}
_MapK ::
    Iso (Tree (MapK m0 n0) k0)
        (Tree (MapK m1 n1) k1)
        (Tree m0 k0 -> Tree n0 k0)
        (Tree m1 k1 -> Tree n1 k1)
_MapK = iso runMapK MkMapK

class KFunctor k where
    -- | Map child values given a mapping function per child type
    mapC ::
        Tree (NodeTypesOf k) (MapK m n) ->
        Tree k m ->
        Tree k n

class KFunctor k => KApply k where
    -- | Combine child values given a combining function per child type
    zipK ::
        Tree k a ->
        Tree k b ->
        Tree k (Both a b)

class    (KPointed k, KApply k) => KApplicative k
instance (KPointed k, KApply k) => KApplicative k

instance HasNodes (Const a) where
    type NodeTypesOf (Const a) = Const ()
    {-# INLINE mNoChildren #-}
    mNoChildren = Just (\(Const x) -> Const x)

instance Monoid a => KPointed (Const a) where
    type KLiftConstraint (Const a) c = ()
    {-# INLINE pureC #-}
    pureC _ = Const mempty
    {-# INLINE pureK #-}
    pureK _ = Const mempty
    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint _ _ = Const mempty

instance KFunctor (Const a) where
    {-# INLINE mapC #-}
    mapC _ (Const x) = Const x

instance Semigroup a => KApply (Const a) where
    {-# INLINE zipK #-}
    zipK (Const x) (Const y) = Const (x <> y)

instance
    (HasNodes a, HasNodes b) =>
    HasNodes (Both a b) where
    type NodeTypesOf (Both a b) = Both (NodeTypesOf a) (NodeTypesOf b)

    {-# INLINE hasNodeTypes #-}
    hasNodeTypes p =
        withDict (hasNodeTypes (pa p)) $
        withDict (hasNodeTypes (pb p)) Dict
        where
            pa :: Proxy (Both a b) -> Proxy a
            pa _ = Proxy
            pb :: Proxy (Both a b) -> Proxy b
            pb _ = Proxy

instance (KPointed a, KPointed b) => KPointed (Both a b) where
    type KLiftConstraint (Both a b) c = (KLiftConstraint a c, KLiftConstraint b c)
    {-# INLINE pureC #-}
    pureC (Both x y) = Both (pureC x) (pureC y)
    {-# INLINE pureK #-}
    pureK f = Both (pureK f) (pureK f)
    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f = Both (pureKWithConstraint p f) (pureKWithConstraint p f)

instance (KFunctor a, KFunctor b) => KFunctor (Both a b) where
    {-# INLINE mapC #-}
    mapC (Both fx fy) (Both x y) = Both (mapC fx x) (mapC fy y)

instance (KApply a, KApply b) => KApply (Both a b) where
    {-# INLINE zipK #-}
    zipK (Both a0 b0) (Both a1 b1) = Both (zipK a0 a1) (zipK b0 b1)

{-# INLINE mapK #-}
mapK ::
    (KFunctor k, HasNodes k) =>
    (forall c. Tree m c -> Tree n c) ->
    Tree k m ->
    Tree k n
mapK f x =
    withDict (hasNodeTypes (p x)) $
    mapC (pureK (MkMapK f)) x
    where
        p :: Tree k l -> Proxy k
        p _ = Proxy

{-# INLINE liftK2 #-}
liftK2 ::
    (KApply k, HasNodes k) =>
    (forall c. Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2 f x = mapK (\(Both a b) -> f a b) . zipK x