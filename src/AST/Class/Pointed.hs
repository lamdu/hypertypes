{-# LANGUAGE RankNTypes #-}

module AST.Class.Pointed
    ( KPointed(..)
    ) where

import AST.Class.Nodes (KNodes(..))
import AST.Knot (Tree)
import Data.Constraint.List (NoConstraint)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

class KNodes k => KPointed k where
    -- | Construct a value from a higher ranked child value
    pureK ::
        (forall child. Tree n child) ->
        Tree k n
    -- TODO: Move this out of class to method?
    pureK f =
        kNoConstraints (Proxy @k) $
        pureKWith (Proxy @NoConstraint) f

    -- | Construct a value from a higher ranked child value with a constraint
    pureKWith ::
        NodesConstraint k constraint =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child) ->
        Tree k n

instance Monoid a => KPointed (Const a) where
    {-# INLINE pureKWith #-}
    pureKWith _ _ = Const mempty

instance (KPointed a, KPointed b) => KPointed (Product a b) where
    {-# INLINE pureKWith #-}
    pureKWith p f = Pair (pureKWith p f) (pureKWith p f)
