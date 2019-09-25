{-# LANGUAGE EmptyCase #-}

-- | A class for lifting constraints to child nodes of a 'AHyperType'.

module Hyper.Class.Nodes
    ( HNodes(..), HWitness(..)
    , (#>), (#*#)
    ) where

import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))
import Hyper.Type (HyperType)

-- | 'HNodes' allows lifting a constraint to the child nodes of a 'AHyperType'
-- by using the 'HNodesConstraint' type family.
--
-- It also provides some methods to combine and process child node constraints.
--
-- Various classes like 'Hyper.Class.Functor.HFunctor' build upon 'HNodes'
-- to provide methods such as 'Hyper.Class.Functor.mapHWith' which provide a rank-n function
-- for processing child nodes which requires a constraint on the nodes.
class HNodes (h :: HyperType) where
    -- | Lift a constraint to apply to the child nodes
    type family HNodesConstraint h (c :: (HyperType -> Constraint)) :: Constraint

    -- | @HWitness h n@ is a witness that @n@ is a node of @h@
    data family HWitness h :: HyperType -> Type

    -- | Lift a rank-n value with a constraint which the child nodes satisfy
    -- to a function from a node witness.
    kLiftConstraint ::
        HNodesConstraint h c =>
        HWitness h n ->
        Proxy c ->
        (c n => r) ->
        r

instance HNodes (Const a) where
    type HNodesConstraint (Const a) x = ()
    data HWitness (Const a) i
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint = \case{}

instance (HNodes a, HNodes b) => HNodes (Product a b) where
    type HNodesConstraint (Product a b) x = (HNodesConstraint a x, HNodesConstraint b x)
    data HWitness (Product a b) n where
        E_Product_a :: HWitness a n -> HWitness (Product a b) n
        E_Product_b :: HWitness b n -> HWitness (Product a b) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (E_Product_a w) = kLiftConstraint w
    kLiftConstraint (E_Product_b w) = kLiftConstraint w

instance (HNodes a, HNodes b) => HNodes (Sum a b) where
    type HNodesConstraint (Sum a b) x = (HNodesConstraint a x, HNodesConstraint b x)
    data HWitness (Sum a b) n where
        E_Sum_a :: HWitness a n -> HWitness (Sum a b) n
        E_Sum_b :: HWitness b n -> HWitness (Sum a b) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (E_Sum_a w) = kLiftConstraint w
    kLiftConstraint (E_Sum_b w) = kLiftConstraint w

infixr 0 #>
infixr 0 #*#

-- | @Proxy @c #> r@ replaces the witness parameter of @r@ with a constraint on the witnessed node
{-# INLINE (#>) #-}
(#>) ::
    (HNodes h, HNodesConstraint h c) =>
    Proxy c -> (c n => r) -> HWitness h n -> r
(#>) p r w = kLiftConstraint w p r

-- | A variant of '#>' which does not consume the witness parameter.
--
-- @Proxy @c0 #*# Proxy @c1 #> r@ brings into context both the @c0 n@ and @c1 n@ constraints.
{-# INLINE (#*#) #-}
(#*#) ::
    (HNodes h, HNodesConstraint h c) =>
    Proxy c -> (HWitness h n -> (c n => r)) -> HWitness h n -> r
(#*#) p r w = (p #> r) w w
