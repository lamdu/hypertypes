-- | A variant of 'Functor' for 'Hyper.Type.HyperType's

{-# LANGUAGE DefaultSignatures, FlexibleContexts, GeneralizedNewtypeDeriving #-}

module Hyper.Class.Functor
    ( HFunctor(..)
    , hmapped1
    ) where

import Control.Lens (Setter, sets)
import Control.Lens.Operators
import Data.Functor.Const (Const(..))
import GHC.Generics
import Data.Proxy (Proxy(..))
import Hyper.Class.Nodes (HNodes(..), HWitness(..), _HWitness, (#>))
import Hyper.Type (Tree)

import Prelude.Compat

-- | A variant of 'Functor' for 'HyperType's
class HNodes h => HFunctor h where
    -- | 'HFunctor' variant of 'fmap'
    --
    -- Applied a given mapping for @h@'s nodes (trees along witnesses that they are nodes of @h@)
    -- to result with a new tree, potentially with a different nest type.
    hmap ::
        (forall n. HWitness h n -> Tree p n -> Tree q n) ->
        Tree h p ->
        Tree h q
    {-# INLINE hmap #-}
    default hmap ::
        (Generic1 h, HFunctor (Rep1 h), HWitnessType h ~ HWitnessType (Rep1 h)) =>
        (forall n. HWitness h n -> Tree p n -> Tree q n) ->
        Tree h p ->
        Tree h q
    hmap f = to1 . hmap (f . (_HWitness %~ id)) . from1

instance HFunctor (Const a) where
    {-# INLINE hmap #-}
    hmap _ (Const x) = Const x

instance (HFunctor a, HFunctor b) => HFunctor (a :*: b) where
    {-# INLINE hmap #-}
    hmap f (x :*: y) =
        hmap (f . HWitness . L1) x :*:
        hmap (f . HWitness . R1) y

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
    Setter (Tree h p) (Tree h q) (Tree p n) (Tree q n)
hmapped1 = sets (\f -> hmap (Proxy @((~) n) #> f))
