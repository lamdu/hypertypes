-- | An extension of 'HFunctor' for parameterized 'Hyper.Type.HyperType's

module Hyper.Class.Morph
    ( HMorph(..), HMorphWithConstraint, morphTraverse, (#?>)
    ) where

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
