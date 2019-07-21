{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds #-}

module AST.Class.Traversable
    ( KTraversable(..)
    , ContainedK(..), _ContainedK
    ) where

import AST.Class.Foldable (KFoldable)
import AST.Class.Functor (KFunctor)
import AST.Knot (Knot, Tree)
import Control.Lens (Iso, iso)
import Data.Functor.Const (Const(..))

import Prelude.Compat

newtype ContainedK f l (k :: Knot) = MkContainedK { runContainedK :: f (l k) }

_ContainedK ::
    Iso (Tree (ContainedK f0 l0) k0)
        (Tree (ContainedK f1 l1) k1)
        (f0 (Tree l0 k0))
        (f1 (Tree l1 k1))
_ContainedK = iso runContainedK MkContainedK

class (KFunctor k, KFoldable k) => KTraversable k where
    sequenceC ::
        Applicative f =>
        Tree k (ContainedK f l) -> f (Tree k l)

instance KTraversable (Const a) where
    sequenceC (Const x) = pure (Const x)
