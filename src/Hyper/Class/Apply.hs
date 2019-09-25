-- | A variant of 'Data.Functor.Apply.Apply' for 'Hyper.Type.AHyperType's

{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

module Hyper.Class.Apply
    ( HApply(..), HApplicative
    , liftH2
    ) where

import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Class.Pointed (HPointed)
import Hyper.Type (Tree)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))

import Prelude.Compat

-- | A variant of 'Data.Functor.Apply.Apply' for 'Hyper.Type.AHyperType's.
--
-- A type which has 'HApply' and 'HPointed' instances also has 'HApplicative',
-- which is the equivalent to the 'Applicative' class.
class HFunctor k => HApply k where
    -- | Combine child values
    --
    -- >>> zipK (Person name0 age0) (Person name1 age1)
    -- Person (Pair name0 name1) (Pair age0 age1)
    zipK ::
        Tree k p ->
        Tree k q ->
        Tree k (Product p q)

-- | A variant of 'Applicative' for 'Hyper.Type.AHyperType's.
class    (HPointed k, HApply k) => HApplicative k
instance (HPointed k, HApply k) => HApplicative k

instance Semigroup a => HApply (Const a) where
    {-# INLINE zipK #-}
    zipK (Const x) (Const y) = Const (x <> y)

instance (HApply a, HApply b) => HApply (Product a b) where
    {-# INLINE zipK #-}
    zipK (Pair a0 b0) (Pair a1 b1) = Pair (zipK a0 a1) (zipK b0 b1)

-- | 'HApply' variant of 'Control.Applicative.liftA2'
{-# INLINE liftH2 #-}
liftH2 ::
    HApply k =>
    (forall n. HWitness k n -> Tree p n -> Tree q n -> Tree r n) ->
    Tree k p ->
    Tree k q ->
    Tree k r
liftH2 f x = mapK (\w (Pair a b) -> f w a b) . zipK x
