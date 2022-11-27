-- | A variant of 'Data.Functor.Apply.Apply' for 'Hyper.Type.HyperType's
module Hyper.Class.Apply
    ( HApply (..)
    , HApplicative
    , liftH2
    ) where

import Hyper.Class.Functor (HFunctor (..))
import Hyper.Class.Nodes (HWitness)
import Hyper.Class.Pointed (HPointed)
import Hyper.Type (type (#))

import Hyper.Internal.Prelude

-- | A variant of 'Data.Functor.Apply.Apply' for 'Hyper.Type.HyperType's.
--
-- A type which has 'HApply' and 'HPointed' instances also has 'HApplicative',
-- which is the equivalent to the 'Applicative' class.
class HFunctor h => HApply h where
    -- | Combine child values
    --
    -- >>> hzip (Person name0 age0) (Person name1 age1)
    -- Person (Pair name0 name1) (Pair age0 age1)
    hzip ::
        h # p ->
        h # q ->
        h # (p :*: q)

-- | A variant of 'Applicative' for 'Hyper.Type.HyperType's.
type HApplicative h = (HPointed h, HApply h)

instance Semigroup a => HApply (Const a) where
    {-# INLINE hzip #-}
    hzip (Const x) (Const y) = Const (x <> y)

instance (HApply a, HApply b) => HApply (a :*: b) where
    {-# INLINE hzip #-}
    hzip (a0 :*: b0) (a1 :*: b1) = hzip a0 a1 :*: hzip b0 b1

-- | 'HApply' variant of 'Control.Applicative.liftA2'
{-# INLINE liftH2 #-}
liftH2 ::
    HApply h =>
    (forall n. HWitness h n -> p # n -> q # n -> r # n) ->
    h # p ->
    h # q ->
    h # r
liftH2 f x = hmap (\w (a :*: b) -> f w a b) . hzip x
