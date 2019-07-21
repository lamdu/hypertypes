{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds, FlexibleInstances #-}

module AST.Class.Applicative
    ( KApplicative(..)
    , LiftK2(..), _LiftK2
    ) where

import AST.Class.Functor (KFunctor)
import AST.Class.Pointed (KPointed)
import AST.Knot (Knot, Tree, ChildrenTypesOf)
import Control.Lens (Iso, iso)
import Data.Functor.Const (Const(..))

newtype LiftK2 l m n (k :: Knot) = MkLiftK2 { runLiftK2 :: l k -> m k -> n k }

_LiftK2 ::
    Iso (Tree (LiftK2 l0 m0 n0) k0)
        (Tree (LiftK2 l1 m1 n1) k1)
        (Tree l0 k0 -> Tree m0 k0 -> Tree n0 k0)
        (Tree l1 k1 -> Tree m1 k1 -> Tree n1 k1)
_LiftK2 = iso runLiftK2 MkLiftK2

class (KPointed k, KFunctor k) => KApplicative k where
    -- | Combine child values given a combining function per child type
    liftC2 ::
        Tree (ChildrenTypesOf k) (LiftK2 l m n) ->
        Tree k l ->
        Tree k m ->
        Tree k n

instance KApplicative (Const ()) where
    liftC2 _ _ _ = Const ()