{-# LANGUAGE FlexibleInstances #-}

-- | An extension of 'HFunctor' for parameterized 'Hyper.Type.HyperType's

module Hyper.Class.Morph
    ( HMorph(..), HMorphWithConstraint
    , morphTraverse, (#?>)
    , HIs2, morphMapped1, morphTraverse1
    ) where

import Control.Lens (Setter, sets)
import Data.Kind (Type)
import Hyper.Class.Traversable (HTraversable(..), ContainedH(..))
import Hyper.Type (type (#), HyperType)

import Hyper.Internal.Prelude

-- | A type-varying variant of 'HFunctor' which can modify type parameters of the mapped 'HyperType'
class HMorph s t where
    type family MorphConstraint s t (c :: (HyperType -> HyperType -> Constraint)) :: Constraint

    data family MorphWitness s t :: HyperType -> HyperType -> Type

    morphMap ::
        (forall a b. MorphWitness s t a b -> p # a -> q # b) ->
        s # p ->
        t # q

    morphLiftConstraint ::
        MorphConstraint s t c =>
        MorphWitness s t a b ->
        Proxy c ->
        (c a b => r) ->
        r

type HMorphWithConstraint s t c = (HMorph s t, MorphConstraint s t c)

-- | 'HTraversable' extended with support of changing type parameters of the 'HyperType'
morphTraverse ::
    (Applicative f, HMorph s t, HTraversable t) =>
    (forall a b. MorphWitness s t a b -> p # a -> f (q # b)) ->
    s # p ->
    f (t # q)
morphTraverse f = hsequence . morphMap (fmap MkContainedH . f)

(#?>) ::
    (HMorph s t, MorphConstraint s t c) =>
    Proxy c -> (c a b => r) -> MorphWitness s t a b -> r
(#?>) p r w = morphLiftConstraint w p r

class (i0 ~ t0, i1 ~ t1) => HIs2 (i0 :: HyperType) (i1 :: HyperType) t0 t1
instance HIs2 a b a b

morphMapped1 ::
    forall a b s t p q.
    HMorphWithConstraint s t (HIs2 a b) =>
    Setter (s # p) (t # q) (p # a) (q # b)
morphMapped1 = sets (\f -> morphMap (Proxy @(HIs2 a b) #?> f))

morphTraverse1 ::
    (HMorphWithConstraint s t (HIs2 a b), HTraversable t) =>
    Traversal (s # p) (t # q) (p # a) (q # b)
morphTraverse1 f = hsequence . (morphMapped1 %~ MkContainedH . f)
