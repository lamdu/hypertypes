{-# LANGUAGE RankNTypes #-}

module AST.Class.Functor
    ( KFunctor(..)
    , mappedK1
    ) where

import AST.Class.Nodes (KNodes(..))
import AST.Knot (Tree)
import Control.Lens (Setter, sets)
import Data.Constraint (withDict)
import Data.Constraint.List (NoConstraint)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A variant of 'Functor' for 'AST.Knot.Knot's.
class KNodes k => KFunctor k where
    -- | 'KFunctor' variant of 'fmap'
    mapK ::
        (forall c. Tree m c -> Tree n c) ->
        Tree k m ->
        Tree k n
    {-# INLINE mapK #-}
    mapK f =
        withDict (kNoConstraints (Proxy @k)) $
        mapKWith (Proxy @NoConstraint) f

    -- | 'KFunctor' variant of 'fmap' for functions with context
    mapKWith ::
        NodesConstraint k constraint =>
        Proxy constraint ->
        (forall c. constraint c => Tree m c -> Tree n c) ->
        Tree k m ->
        Tree k n

instance KFunctor (Const a) where
    {-# INLINE mapKWith #-}
    mapKWith _ _ (Const x) = Const x

instance (KFunctor a, KFunctor b) => KFunctor (Product a b) where
    {-# INLINE mapKWith #-}
    mapKWith p f (Pair x y) =
        Pair (mapKWith p f x) (mapKWith p f y)

-- | 'KFunctor' variant of 'Control.Lens.mapped' for 'AST.Knot.Knot's with a single node type.
--
-- Avoids using `RankNTypes` and thus can be composed with other optics.
{-# INLINE mappedK1 #-}
mappedK1 ::
    forall k c m n.
    (KFunctor k, NodesConstraint k ((~) c)) =>
    Setter (Tree k m) (Tree k n) (Tree m c) (Tree n c)
mappedK1 = sets (mapKWith (Proxy @((~) c)))
