{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds #-}

module AST.Class.Functor
    ( KFunctor(..), MapK(..), _MapK
    ) where

import AST.Knot (Knot, Tree, ChildrenTypesOf)
import Control.Lens (Lens)
import Control.Lens.Operators ((<&>))

newtype MapK m n (k :: Knot) = MkMapK { runMapK :: m k -> n k }

_MapK ::
    Lens
        (Tree (MapK m0 n0) k0)
        (Tree (MapK m1 n1) k1)
        (Tree m0 k0 -> Tree n0 k0)
        (Tree m1 k1 -> Tree n1 k1)
_MapK f (MkMapK x) = f x <&> MkMapK

class KFunctor k where
    -- | Map child values given a mapping function per child type
    mapC ::
        Tree (ChildrenTypesOf k) (MapK m n) ->
        Tree k m -> Tree k n
