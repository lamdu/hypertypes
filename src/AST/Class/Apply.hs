{-# LANGUAGE NoImplicitPrelude, FlexibleInstances #-}

module AST.Class.Apply
    ( KApply(..)
    ) where

import AST.Class (KFunctor)
import AST.Combinator.Both (Both(..))
import AST.Knot (Tree)
import Data.Functor.Const (Const(..))

import Prelude.Compat

class KFunctor k => KApply k where
    -- | Combine child values given a combining function per child type
    zipK ::
        Tree k a ->
        Tree k b ->
        Tree k (Both a b)

instance Semigroup a => KApply (Const a) where
    {-# INLINE zipK #-}
    zipK (Const x) (Const y) = Const (x <> y)

instance (KApply a, KApply b) => KApply (Both a b) where
    {-# INLINE zipK #-}
    zipK (Both a0 b0) (Both a1 b1) = Both (zipK a0 a1) (zipK b0 b1)
