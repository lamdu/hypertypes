{-# LANGUAGE GADTs, RankNTypes, EmptyCase #-}

module AST.Class.Nodes
    ( KNodes(..), KWitness(..)
    , (#>), (#*#)
    ) where

import AST.Knot (Knot)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
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
    kLiftConstraint = \case

instance (KNodes a, KNodes b) => KNodes (Product a b) where
    type KNodesConstraint (Product a b) x = (KNodesConstraint a x, KNodesConstraint b x)
    data KWitness (Product a b) n where
        KW_Product_E0 :: KWitness a n -> KWitness (Product a b) n
        KW_Product_E1 :: KWitness b n -> KWitness (Product a b) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (KW_Product_E0 w) = kLiftConstraint w
    kLiftConstraint (KW_Product_E1 w) = kLiftConstraint w

infixr 0 #>
infixr 0 #*#

{-# INLINE (#>) #-}
(#>) ::
    (KNodes k, KNodesConstraint k c) =>
    Proxy c -> (c n => r) -> KWitness k n -> r
(#>) p r w = kLiftConstraint w p r

(#*#) ::
    (KNodes k, KNodesConstraint k c) =>
    Proxy c -> (KWitness k n -> (c n => r)) -> KWitness k n -> r
(#*#) p r w = kLiftConstraint w p r w
