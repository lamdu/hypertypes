{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module AST.Class
    ( KNodes(..)
    , KPointed(..)
    ) where

import AST.Knot (Knot, Tree)
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

class KNodes k => KPointed k where
    -- | Construct a value from a higher ranked child value
    pureK ::
        (forall child. Tree n child) ->
        Tree k n

    -- | Construct a value from a higher ranked child value with a constraint
    pureKWith ::
        NodesConstraint k constraint =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child) ->
        Tree k n

instance KNodes (Const a) where
    type NodesConstraint (Const a) x = ()
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = Dict

instance Monoid a => KPointed (Const a) where
    {-# INLINE pureK #-}
    pureK _ = Const mempty
    {-# INLINE pureKWith #-}
    pureKWith _ _ = Const mempty

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

instance (KPointed a, KPointed b) => KPointed (Product a b) where
    {-# INLINE pureK #-}
    pureK f = Pair (pureK f) (pureK f)
    {-# INLINE pureKWith #-}
    pureKWith p f = Pair (pureKWith p f) (pureKWith p f)
