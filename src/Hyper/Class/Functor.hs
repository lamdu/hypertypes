{-# LANGUAGE FlexibleContexts #-}

-- | A variant of 'Functor' for 'Hyper.Type.HyperType's
module Hyper.Class.Functor
    ( HFunctor (..)
    , hmapped1
    , hiso
    ) where

import Control.Lens (AnIso', Iso', Setter, cloneIso, iso, sets, _Wrapped)
import GHC.Generics
import GHC.Generics.Lens (generic1)
import Hyper.Class.Nodes (HNodes (..), HWitness (..), (#>), _HWitness)
import Hyper.Type (type (#))

import Hyper.Internal.Prelude

-- | A variant of 'Functor' for 'HyperType's
class HNodes h => HFunctor h where
    -- | 'HFunctor' variant of 'fmap'
    --
    -- Applied a given mapping for @h@'s nodes (trees along witnesses that they are nodes of @h@)
    -- to result with a new tree, potentially with a different nest type.
    hmap ::
        (forall n. HWitness h n -> p # n -> q # n) ->
        h # p ->
        h # q
    {-# INLINE hmap #-}
    default hmap ::
        (Generic1 h, HFunctor (Rep1 h), HWitnessType h ~ HWitnessType (Rep1 h)) =>
        (forall n. HWitness h n -> p # n -> q # n) ->
        h # p ->
        h # q
    hmap f = generic1 %~ hmap (f . (_HWitness %~ id))

instance HFunctor (Const a) where
    {-# INLINE hmap #-}
    hmap _ = _Wrapped %~ id

instance (HFunctor a, HFunctor b) => HFunctor (a :*: b) where
    {-# INLINE hmap #-}
    hmap f (x :*: y) =
        hmap (f . HWitness . L1) x
            :*: hmap (f . HWitness . R1) y

instance (HFunctor a, HFunctor b) => HFunctor (a :+: b) where
    {-# INLINE hmap #-}
    hmap f (L1 x) = L1 (hmap (f . HWitness . L1) x)
    hmap f (R1 x) = R1 (hmap (f . HWitness . R1) x)

deriving newtype instance HFunctor h => HFunctor (M1 i m h)
deriving newtype instance HFunctor h => HFunctor (Rec1 h)

-- | 'HFunctor' variant of 'Control.Lens.mapped' for 'Hyper.Type.HyperType's with a single node type.
--
-- Avoids using @RankNTypes@ and thus can be composed with other optics.
{-# INLINE hmapped1 #-}
hmapped1 ::
    forall h n p q.
    (HFunctor h, HNodesConstraint h ((~) n)) =>
    Setter (h # p) (h # q) (p # n) (q # n)
hmapped1 = sets (\f -> hmap (Proxy @((~) n) #> f))

-- | Define 'Iso's for 'HFunctor's
--
-- TODO: Is there an equivalent for this in lens that we can name this after?
hiso ::
    HFunctor h =>
    (forall n. HWitness h n -> AnIso' (p # n) (q # n)) ->
    Iso' (h # p) (h # q)
hiso f = iso (hmap (\w -> (^. cloneIso (f w)))) (hmap (\w -> (cloneIso (f w) #)))
