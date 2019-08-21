{-# LANGUAGE ScopedTypeVariables #-}

module AST.Class.Nodes (KNodes(..)) where

import AST.Knot (Knot)
import Data.Constraint
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Constraint.List (And)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class KNodes (k :: Knot -> Type) where
    -- | Lift a constraint to apply to the node types.
    type family NodesConstraint k (c :: ((Knot -> Type) -> Constraint)) :: Constraint

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
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p =
        withDict (kCombineConstraints (p0 p)) $
        withDict (kCombineConstraints (p1 p)) Dict
        where
            p0 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 a)
            p0 _ = Proxy
            p1 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 b)
            p1 _ = Proxy
