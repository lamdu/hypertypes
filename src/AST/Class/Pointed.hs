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
    -- | Construct a value from a higher ranked child value
    pureK ::
        (forall c. KWitness k c -> Tree n c) ->
        Tree k n

instance Monoid a => KPointed (Const a) where
    {-# INLINE pureK #-}
    pureK _ = Const mempty

instance (KPointed a, KPointed b) => KPointed (Product a b) where
    {-# INLINE pureK #-}
    pureK f = Pair (pureK (f . KWitness_Product_E0)) (pureK (f . KWitness_Product_E1))

-- | Construct a value from a higher ranked child value with a constraint
pureKWith ::
    (KPointed k, NodesConstraint k constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Tree n child) ->
    Tree k n
pureKWith p f = pureK (kLiftConstraint p f)
