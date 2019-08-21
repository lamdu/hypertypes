{-# LANGUAGE DefaultSignatures, RankNTypes #-}
{-# OPTIONS -Wno-redundant-constraints #-} -- Work around false GHC warnings

module AST.Class.Nodes (KNodes(..)) where

import AST.Knot (Knot)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Constraint.List (NoConstraint, And)
import Data.Kind (Type, Constraint)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class KNodes (k :: Knot -> Type) where
    -- | Lift a constraint to apply to the node types.
    type family NodesConstraint k (c :: ((Knot -> Type) -> Constraint)) :: Constraint

    kNoConstraints :: Proxy k -> (NodesConstraint k NoConstraint => r) -> r
    {-# INLINE kNoConstraints #-}
    default kNoConstraints ::
        NodesConstraint k NoConstraint =>
        Proxy k -> (NodesConstraint k NoConstraint => r) -> r
    kNoConstraints _ = id

    kCombineConstraints ::
        (NodesConstraint k a, NodesConstraint k b) =>
        Proxy (And a b k) ->
        (NodesConstraint k (And a b) => r) ->
        r

instance KNodes (Const a) where
    type NodesConstraint (Const a) x = ()
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = id

instance (KNodes a, KNodes b) => KNodes (Product a b) where
    type NodesConstraint (Product a b) x = (NodesConstraint a x, NodesConstraint b x)
    {-# INLINE kNoConstraints #-}
    kNoConstraints _ x =
        kNoConstraints (Proxy @a) $
        kNoConstraints (Proxy @b) x
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p x =
        kCombineConstraints (p0 p) $
        kCombineConstraints (p1 p) x
        where
            p0 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 a)
            p0 _ = Proxy
            p1 :: Proxy (And c0 c1 (Product a b)) -> Proxy (And c0 c1 b)
            p1 _ = Proxy
