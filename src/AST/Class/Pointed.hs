{-# LANGUAGE RankNTypes #-}

module AST.Class.Pointed
    ( KPointed(..), pureKWith
    ) where

import AST.Class.Nodes (KNodes(..), KWitness(..))
import AST.Knot (Tree)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A variant of 'Data.Pointed.Pointed' for 'AST.Knot.Knot's
class KNodes k => KPointed k where
    -- | Construct a value from a generator of @k@'s nodes
    -- (a generator which can generate a tree of any type given a witness that it is a node of @k@)
    pureK ::
        (forall n. KWitness k n -> Tree p n) ->
        Tree k p

instance Monoid a => KPointed (Const a) where
    {-# INLINE pureK #-}
    pureK _ = Const mempty

instance (KPointed a, KPointed b) => KPointed (Product a b) where
    {-# INLINE pureK #-}
    pureK f = Pair (pureK (f . KW_Product_E0)) (pureK (f . KW_Product_E1))

-- | Variant of 'pureK' for functions with context instead of a witness parameter
pureKWith ::
    (KPointed k, KNodesConstraint k constraint) =>
    Proxy constraint ->
    (forall n. constraint n => Tree p n) ->
    Tree k p
pureKWith p f = pureK (\w -> kLiftConstraint w p f)
