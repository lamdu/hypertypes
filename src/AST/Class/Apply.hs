{-# LANGUAGE RankNTypes, FlexibleInstances, UndecidableInstances #-}

module AST.Class.Apply
    ( KApply(..), KApplicative
    , liftK2, liftK2With
    ) where

import AST.Class.Functor (KFunctor(..), mapKWith)
import AST.Class.Nodes (KNodes(..))
import AST.Class.Pointed (KPointed)
import AST.Knot (Tree)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Proxy (Proxy)

import Prelude.Compat

-- | A variant of 'Data.Functor.Apply.Apply' for 'AST.Knot.Knot's.
--
-- A type which has 'KApply' and 'KPointed' instances also has 'KApplicative',
-- which is the equivalent to the 'Applicative' class.
class KFunctor k => KApply k where
    -- | Combine child values
    --
    -- >>> zipK (Person name0 age0) (Person name1 age1)
    -- Person (Pair name0 name1) (Pair age0 age1)
    zipK ::
        Tree k a ->
        Tree k b ->
        Tree k (Product a b)

-- | A variant of 'Applicative' for 'AST.Knot.Knot's.
class    (KPointed k, KApply k) => KApplicative k
instance (KPointed k, KApply k) => KApplicative k

instance Semigroup a => KApply (Const a) where
    {-# INLINE zipK #-}
    zipK (Const x) (Const y) = Const (x <> y)

instance (KApply a, KApply b) => KApply (Product a b) where
    {-# INLINE zipK #-}
    zipK (Pair a0 b0) (Pair a1 b1) = Pair (zipK a0 a1) (zipK b0 b1)

-- | 'KApply' variant of 'Control.Applicative.liftA2'
{-# INLINE liftK2 #-}
liftK2 ::
    KApply k =>
    (forall c. Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2 f x = mapK (const (\(Pair a b) -> f a b)) . zipK x

-- | 'KApply' variant of 'Control.Applicative.liftA2' for functions with context
{-# INLINE liftK2With #-}
liftK2With ::
    (KApply k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall c. constraint c => Tree l c -> Tree m c -> Tree n c) ->
    Tree k l ->
    Tree k m ->
    Tree k n
liftK2With p f x = mapKWith p (\(Pair a b) -> f a b) . zipK x
