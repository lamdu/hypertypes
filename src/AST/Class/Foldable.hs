{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds #-}

module AST.Class.Foldable
    ( KFoldable(..)
    , ConvertK(..), _ConvertK
    ) where

import AST.Class (NodeTypesOf)
import AST.Knot
import Control.Lens (Iso, iso)
import Data.Functor.Const (Const(..))

import Prelude.Compat

newtype ConvertK a l (k :: Knot) = MkConvertK { runConvertK :: l k -> a }

{-# INLINE _ConvertK #-}
_ConvertK ::
    Iso (Tree (ConvertK a0 l0) k0)
        (Tree (ConvertK a1 l1) k1)
        (Tree l0 k0 -> a0)
        (Tree l1 k1 -> a1)
_ConvertK = iso runConvertK MkConvertK

class KFoldable k where
    foldMapC ::
        Monoid a =>
        Tree (NodeTypesOf k) (ConvertK a l) ->
        Tree k l ->
        a

instance KFoldable (Const a) where
    {-# INLINE foldMapC #-}
    foldMapC _ _ = mempty
