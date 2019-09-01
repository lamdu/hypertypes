{-# LANGUAGE DefaultSignatures #-}

module AST.Class.Nodes (KNodes(..)) where

import AST.Knot (Knot)
import Data.Constraint
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Constraint.List (NoConstraint, And)
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
--
-- The 'kNoConstraints' method represents the constraint that 'NoConstraint' applies to the child nodes.
-- It replaces context for 'KNodes' to avoid @UndecidableSuperClasses@.
-- Instances usually don't need to implement this method
-- as the default implementation provide usually works for them.
class KNodes (k :: Knot -> Type) where
    -- | Lift a constraint to apply to the child nodes
    type family NodesConstraint k (c :: ((Knot -> Type) -> Constraint)) :: Constraint

    -- TODO: Putting documentation here causes duplication in the haddock documentation
    kNoConstraints :: Proxy k -> Dict (NodesConstraint k NoConstraint)
    {-# INLINE kNoConstraints #-}
    default kNoConstraints ::
        NodesConstraint k NoConstraint =>
        Proxy k -> Dict (NodesConstraint k NoConstraint)
    kNoConstraints _ = Dict

    -- | Combine two 'NodesConstraint' to allow
    -- processing child nodes with functions that require both constraints
    kCombineConstraints ::
        (NodesConstraint k a, NodesConstraint k b) =>
        Proxy (And a b k) ->
        Dict (NodesConstraint k (And a b))

instance KNodes (Const a) where
    type NodesConstraint (Const a) x = ()
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = Dict

instance (KNodes a, KNodes b) => KNodes (Product a b) where
    type NodesConstraint (Product a b) x = (NodesConstraint a x, NodesConstraint b x)
    {-# INLINE kNoConstraints #-}
    kNoConstraints _ =
        withDict (kNoConstraints (Proxy @a)) $
        withDict (kNoConstraints (Proxy @b)) Dict
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p =
        withDict (kCombineConstraints (p0 p)) $
        withDict (kCombineConstraints (p1 p)) Dict
        where
            p0 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 a)
            p0 _ = Proxy
            p1 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 b)
            p1 _ = Proxy
