{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds #-}

module AST.Class.Applicative
    ( KApplicative(..)
    , LiftK2(..), _LiftK2
    ) where

import AST.Class.Functor (KFunctor)
import AST.Class.Pointed (KPointed)
import AST.Knot (Knot, Tree, ChildrenTypesOf)
import Control.Lens (Lens)

import Prelude.Compat

newtype LiftK2 l m n (k :: Knot) = MkLiftK2 { runLiftK2 :: l k -> m k -> n k }

_LiftK2 ::
    Lens
        (Tree (LiftK2 l0 m0 n0) k0)
        (Tree (LiftK2 l1 m1 n1) k1)
        (Tree l0 k0 -> Tree m0 k0 -> Tree n0 k0)
        (Tree l1 k1 -> Tree m1 k1 -> Tree n1 k1)
_LiftK2 f = fmap MkLiftK2 . f . runLiftK2

class (KPointed k, KFunctor k) => KApplicative k where
    -- | Combine child values given a combining function per child type
    liftC2 ::
        Tree (ChildrenTypesOf k) (LiftK2 l m n) ->
        Tree k l ->
        Tree k m ->
        Tree k n
