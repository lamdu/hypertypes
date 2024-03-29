{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A class for witness types and lifting of constraints to the child nodes of a 'HyperType'
module Hyper.Class.Nodes
    ( HNodes (..)
    , HWitness (..)
    , _HWitness
    , (#>)
    , (#*#)
    , HNodesHaveConstraint (..)
    ) where

import Data.Kind (Type)
import GHC.Generics
import Hyper.Type

import Hyper.Internal.Prelude

newtype HWitness h n = HWitness (HWitnessType h n)

-- | 'HNodes' allows talking about the child nodes of a 'HyperType'.
--
-- Various classes like 'Hyper.Class.Functor.HFunctor' build upon 'HNodes'
-- to provide methods such as 'Hyper.Class.Functor.hmap' which provide a rank-n function
-- for processing child nodes which requires a constraint on the nodes.
class HNodes (h :: HyperType) where
    -- | Lift a constraint to apply to the child nodes
    type HNodesConstraint h (c :: (HyperType -> Constraint)) :: Constraint

    type HNodesConstraint h c = HNodesConstraint (Rep1 h) c

    -- | @HWitness h n@ is a witness that @n@ is a node of @h@.
    --
    -- A value quantified with @forall n. HWitness h n -> ... n@,
    -- is equivalent for a "for-some" where the possible values for @n@ are the nodes of @h@.
    type HWitnessType h :: HyperType -> Type

    type HWitnessType h = HWitnessType (Rep1 h)

    -- | Lift a rank-n value with a constraint which the child nodes satisfy
    -- to a function from a node witness.
    hLiftConstraint ::
        HNodesConstraint h c =>
        HWitness h n ->
        Proxy c ->
        (c n => r) ->
        r
    {-# INLINE hLiftConstraint #-}
    default hLiftConstraint ::
        ( HWitnessType h ~ HWitnessType (Rep1 h)
        , HNodesConstraint h c ~ HNodesConstraint (Rep1 h) c
        , HNodes (Rep1 h)
        , HNodesConstraint h c
        ) =>
        HWitness h n ->
        Proxy c ->
        (c n => r) ->
        r
    hLiftConstraint (HWitness w) = hLiftConstraint @(Rep1 h) (HWitness w)

makePrisms ''HWitness

instance HNodes (Const a) where
    type HNodesConstraint (Const a) _ = ()
    type HWitnessType (Const a) = V1
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint = \case {}

instance (HNodes a, HNodes b) => HNodes (a :*: b) where
    type HNodesConstraint (a :*: b) x = (HNodesConstraint a x, HNodesConstraint b x)
    type HWitnessType (a :*: b) = HWitness a :+: HWitness b
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (HWitness (L1 w)) = hLiftConstraint w
    hLiftConstraint (HWitness (R1 w)) = hLiftConstraint w

instance (HNodes a, HNodes b) => HNodes (a :+: b) where
    type HNodesConstraint (a :+: b) x = (HNodesConstraint a x, HNodesConstraint b x)
    type HWitnessType (a :+: b) = HWitness a :+: HWitness b
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (HWitness (L1 w)) = hLiftConstraint w
    hLiftConstraint (HWitness (R1 w)) = hLiftConstraint w

deriving newtype instance HNodes h => HNodes (M1 i m h)
deriving newtype instance HNodes h => HNodes (Rec1 h)

infixr 0 #>
infixr 0 #*#

-- | @Proxy @c #> r@ replaces the witness parameter of @r@ with a constraint on the witnessed node
{-# INLINE (#>) #-}
(#>) ::
    (HNodes h, HNodesConstraint h c) =>
    Proxy c ->
    (c n => r) ->
    HWitness h n ->
    r
(#>) p r w = hLiftConstraint w p r

-- | A variant of '#>' which does not consume the witness parameter.
--
-- @Proxy @c0 #*# Proxy @c1 #> r@ brings into context both the @c0 n@ and @c1 n@ constraints.
{-# INLINE (#*#) #-}
(#*#) ::
    (HNodes h, HNodesConstraint h c) =>
    Proxy c ->
    (c n => HWitness h n -> r) ->
    HWitness h n ->
    r
(#*#) p r w = (p #> r) w w

-- | Defunctionalized HNodesConstraint which can be curried
class HNodesHaveConstraint c h where
    hNodesHaveConstraint :: proxy0 c -> proxy1 h -> Dict (HNodesConstraint h c)

instance HNodesConstraint h c => HNodesHaveConstraint c h where
    hNodesHaveConstraint _ _ = Dict
