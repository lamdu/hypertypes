{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds, RankNTypes #-}

module AST.Class.Foldable
    ( KFoldable(..)
    , ConvertK(..), _ConvertK
    , foldMapK, traverseK_
    ) where

import AST.Class (NodeTypesOf, HasNodeTypes(..), KPointed(..))
import AST.Knot (Tree, Knot)
import Control.Lens (Iso, iso)
import Data.Foldable (sequenceA_)
import Data.Functor.Const (Const(..))
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

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

{-# INLINE foldMapK #-}
foldMapK ::
    (Monoid a, KFoldable k, HasNodeTypes k) =>
    (forall c. Tree l c -> a) ->
    Tree k l ->
    a
foldMapK f x =
    withDict (hasNodeTypes (p x)) $
    foldMapC (pureK (MkConvertK f)) x
    where
        p :: Tree k l -> Proxy k
        p _ = Proxy

{-# INLINE traverseK_ #-}
traverseK_ ::
    (Applicative f, KFoldable k, HasNodeTypes k) =>
    (forall c. Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK_ f = sequenceA_ . foldMapK ((:[]) . f)
