-- | A class for witness types and lifting of constraints to the child nodes of a 'HyperType'

{-# LANGUAGE EmptyCase #-}

module Hyper.Class.Nodes
    ( HNodes(..), HWitness(..)
    , (#>), (#*#)
    ) where

import Data.Functor.Const (Const(..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))
import GHC.Generics ((:+:)(..), (:*:)(..))
import Hyper.Type (HyperType)

-- | 'HNodes' allows talking about the child nodes of a 'HyperType'.
--
-- Various classes like 'Hyper.Class.Functor.HFunctor' build upon 'HNodes'
-- to provide methods such as 'Hyper.Class.Functor.hmap' which provide a rank-n function
-- for processing child nodes which requires a constraint on the nodes.
class HNodes (h :: HyperType) where
    -- | Lift a constraint to apply to the child nodes
    type family HNodesConstraint h (c :: (HyperType -> Constraint)) :: Constraint

    -- | @HWitness h n@ is a witness that @n@ is a node of @h@.
    --
    -- A value quantified with @forall n. HWitness h n -> ... n@,
    -- is equivalent for a "for-some" where the possible values for @n@ are the nodes of @h@.
    data family HWitness h :: HyperType -> Type

    -- | Lift a rank-n value with a constraint which the child nodes satisfy
    -- to a function from a node witness.
    hLiftConstraint ::
        HNodesConstraint h c =>
        HWitness h n ->
        Proxy c ->
        (c n => r) ->
        r

instance HNodes (Const a) where
    type HNodesConstraint (Const a) x = ()
    data HWitness (Const a) i
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint = \case{}

instance (HNodes a, HNodes b) => HNodes (a :*: b) where
    type HNodesConstraint (a :*: b) x = (HNodesConstraint a x, HNodesConstraint b x)
    data HWitness (a :*: b) n where
        E_Product_a :: HWitness a n -> HWitness (a :*: b) n
        E_Product_b :: HWitness b n -> HWitness (a :*: b) n
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (E_Product_a w) = hLiftConstraint w
    hLiftConstraint (E_Product_b w) = hLiftConstraint w

instance (HNodes a, HNodes b) => HNodes (a :+: b) where
    type HNodesConstraint (a :+: b) x = (HNodesConstraint a x, HNodesConstraint b x)
    data HWitness (a :+: b) n where
        E_Sum_a :: HWitness a n -> HWitness (a :+: b) n
        E_Sum_b :: HWitness b n -> HWitness (a :+: b) n
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (E_Sum_a w) = hLiftConstraint w
    hLiftConstraint (E_Sum_b w) = hLiftConstraint w

infixr 0 #>
infixr 0 #*#

-- | @Proxy @c #> r@ replaces the witness parameter of @r@ with a constraint on the witnessed node
{-# INLINE (#>) #-}
(#>) ::
    (HNodes h, HNodesConstraint h c) =>
    Proxy c -> (c n => r) -> HWitness h n -> r
(#>) p r w = hLiftConstraint w p r

-- | A variant of '#>' which does not consume the witness parameter.
--
-- @Proxy @c0 #*# Proxy @c1 #> r@ brings into context both the @c0 n@ and @c1 n@ constraints.
{-# INLINE (#*#) #-}
(#*#) ::
    (HNodes h, HNodesConstraint h c) =>
    Proxy c -> (HWitness h n -> (c n => r)) -> HWitness h n -> r
(#*#) p r w = (p #> r) w w
