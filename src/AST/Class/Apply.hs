{-# LANGUAGE RankNTypes, FlexibleInstances, UndecidableInstances #-}

module AST.Class.Apply
    ( KApply(..), KApplicative
    , liftK2
    ) where

import AST.Class.Functor (KFunctor(..))
import AST.Class.Nodes (KNodes(..))
import AST.Class.Pointed (KPointed)
import AST.Knot (Tree)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))

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
        Tree k p ->
        Tree k q ->
        Tree k (Product p q)

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
    (forall n. KWitness k n -> Tree p n -> Tree q n -> Tree r n) ->
    Tree k p ->
    Tree k q ->
    Tree k r
liftK2 f x = mapK (\w -> (\(Pair a b) -> f w a b)) . zipK x
