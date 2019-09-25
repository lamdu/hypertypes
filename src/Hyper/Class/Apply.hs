-- | A variant of 'Data.Functor.Apply.Apply' for 'Hyper.Type.AHyperType's

{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

module Hyper.Class.Apply
    ( HApply(..), HApplicative
    , liftH2
    ) where

import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Class.Pointed (HPointed)
import Hyper.Type (Tree)

import Prelude.Compat

-- | A variant of 'Data.Functor.Apply.Apply' for 'Hyper.Type.AHyperType's.
--
-- A type which has 'HApply' and 'HPointed' instances also has 'HApplicative',
-- which is the equivalent to the 'Applicative' class.
class HFunctor h => HApply h where
    -- | Combine child values
    --
    -- >>> zipH (Person name0 age0) (Person name1 age1)
    -- Person (Pair name0 name1) (Pair age0 age1)
    zipH ::
        Tree h p ->
        Tree h q ->
        Tree h (Product p q)

-- | A variant of 'Applicative' for 'Hyper.Type.AHyperType's.
class    (HPointed h, HApply h) => HApplicative h
instance (HPointed h, HApply h) => HApplicative h

instance Semigroup a => HApply (Const a) where
    {-# INLINE zipH #-}
    zipH (Const x) (Const y) = Const (x <> y)

instance (HApply a, HApply b) => HApply (Product a b) where
    {-# INLINE zipH #-}
    zipH (Pair a0 b0) (Pair a1 b1) = Pair (zipH a0 a1) (zipH b0 b1)

-- | 'HApply' variant of 'Control.Applicative.liftA2'
{-# INLINE liftH2 #-}
liftH2 ::
    HApply h =>
    (forall n. HWitness h n -> Tree p n -> Tree q n -> Tree r n) ->
    Tree h p ->
    Tree h q ->
    Tree h r
liftH2 f x = mapH (\w (Pair a b) -> f w a b) . zipH x
