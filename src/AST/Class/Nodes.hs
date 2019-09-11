{-# LANGUAGE GADTs, RankNTypes, EmptyCase #-}

module AST.Class.Nodes
    ( KNodes(..), KWitness(..)
    , (#>), (#*#)
    ) where

import AST.Knot (Knot)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))

-- | 'KNodes' allows lifting a constraint to the child nodes of a 'Knot'
-- by using the 'KNodesConstraint' type family.
--
-- It also provides some methods to combine and process child node constraints.
--
-- Various classes like 'AST.Class.Functor.KFunctor' build upon 'KNodes'
-- to provide methods such as 'AST.Class.Functor.mapKWith' which provide a rank-n function
-- for processing child nodes which requires a constraint on the nodes.
class KNodes (k :: Knot -> Type) where
    -- | Lift a constraint to apply to the child nodes
    type family KNodesConstraint k (c :: ((Knot -> Type) -> Constraint)) :: Constraint

    -- | @KWitness k n@ is a witness that @n@ is a node of @k@
    data family KWitness k :: (Knot -> Type) -> Type

    -- | Lift a rank-n value with a constraint which the child nodes satisfy
    -- to a function from a node witness.
    kLiftConstraint ::
        KNodesConstraint k c =>
        KWitness k n ->
        Proxy c ->
        (c n => r) ->
        r

instance KNodes (Const a) where
    type KNodesConstraint (Const a) x = ()
    data KWitness (Const a) i
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint = \case{}

instance (KNodes a, KNodes b) => KNodes (Product a b) where
    type KNodesConstraint (Product a b) x = (KNodesConstraint a x, KNodesConstraint b x)
    data KWitness (Product a b) n where
        E_Product_a :: KWitness a n -> KWitness (Product a b) n
        E_Product_b :: KWitness b n -> KWitness (Product a b) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (E_Product_a w) = kLiftConstraint w
    kLiftConstraint (E_Product_b w) = kLiftConstraint w

instance (KNodes a, KNodes b) => KNodes (Sum a b) where
    type KNodesConstraint (Sum a b) x = (KNodesConstraint a x, KNodesConstraint b x)
    data KWitness (Sum a b) n where
        E_Sum_a :: KWitness a n -> KWitness (Sum a b) n
        E_Sum_b :: KWitness b n -> KWitness (Sum a b) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (E_Sum_a w) = kLiftConstraint w
    kLiftConstraint (E_Sum_b w) = kLiftConstraint w

infixr 0 #>
infixr 0 #*#

{-# INLINE (#>) #-}
(#>) ::
    (KNodes k, KNodesConstraint k c) =>
    Proxy c -> (c n => r) -> KWitness k n -> r
(#>) p r w = kLiftConstraint w p r

{-# INLINE (#*#) #-}
(#*#) ::
    (KNodes k, KNodesConstraint k c) =>
    Proxy c -> (KWitness k n -> (c n => r)) -> KWitness k n -> r
(#*#) p r w = (p #> r) w w
