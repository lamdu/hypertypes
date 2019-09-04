{-# LANGUAGE GADTs, RankNTypes, EmptyCase #-}

module AST.Class.Nodes
    ( KNodes(..), KWitness(..)
    ) where

import AST.Knot (Knot, Tree)
import Data.Constraint
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Constraint.List (And)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | 'KNodes' allows lifting a constraint to the child nodes of a 'Knot'
-- by using the 'NodesConstraint' type family.
--
-- It also provides some methods to combine and process child node constraints.
--
-- Various classes like 'AST.Class.Functor.KFunctor' build upon 'KNodes'
-- to provide methods such as 'AST.Class.Functor.mapKWith' which provide a rank-n function
-- for processing child nodes which requires a constraint on the nodes.
class KNodes (k :: Knot -> Type) where
    -- | Lift a constraint to apply to the child nodes
    type family NodesConstraint k (c :: ((Knot -> Type) -> Constraint)) :: Constraint

    -- | @KWitness k n@ is a witness that @n@ is a node of @k@
    data family KWitness k :: (Knot -> Type) -> Type

    -- | Lift a rank-n value with a constraint which the child nodes satisfy
    -- to a function from a node witness.
    kLiftConstraint ::
        NodesConstraint k c =>
        Proxy c ->
        KWitness k n ->
        (c n => Tree r n) ->
        Tree r n

    -- | Combine two 'NodesConstraint' to allow
    -- processing child nodes with functions that require both constraints
    kCombineConstraints ::
        (NodesConstraint k a, NodesConstraint k b) =>
        Proxy (And a b k) ->
        Dict (NodesConstraint k (And a b))

instance KNodes (Const a) where
    type NodesConstraint (Const a) x = ()
    data KWitness (Const a) i
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint _ = \case
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = Dict

instance (KNodes a, KNodes b) => KNodes (Product a b) where
    type NodesConstraint (Product a b) x = (NodesConstraint a x, NodesConstraint b x)
    data KWitness (Product a b) n where
        KWitness_Product_E0 :: KWitness a n -> KWitness (Product a b) n
        KWitness_Product_E1 :: KWitness b n -> KWitness (Product a b) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint p (KWitness_Product_E0 w) = kLiftConstraint p w
    kLiftConstraint p (KWitness_Product_E1 w) = kLiftConstraint p w
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p =
        withDict (kCombineConstraints (p0 p)) $
        withDict (kCombineConstraints (p1 p)) Dict
        where
            p0 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 a)
            p0 _ = Proxy
            p1 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 b)
            p1 _ = Proxy
