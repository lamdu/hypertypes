{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds, RankNTypes #-}
{-# LANGUAGE TypeApplications, ScopedTypeVariables #-}

module AST.Class.Foldable
    ( KFoldable(..)
    , ConvertK(..), _ConvertK
    , foldMapK, foldMapKWith
    , traverseK_, traverseKWith_
    ) where

import AST.Class (NodeTypesOf, KNodes(..), KPointed(..))
import AST.Class.Combinators (KLiftConstraints(..), ApplyKConstraints, pureKWith)
import AST.Knot (Tree, Knot)
import Control.Lens (Iso, iso)
import Control.Lens.Operators
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

class KNodes k => KFoldable k where
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
    forall a k l.
    (Monoid a, KFoldable k) =>
    (forall c. Tree l c -> a) ->
    Tree k l ->
    a
foldMapK f x =
    withDict (kNodes (Proxy :: Proxy k)) $
    foldMapC (pureK (MkConvertK f)) x

{-# INLINE foldMapKWith #-}
foldMapKWith ::
    forall a k n constraints.
    (Monoid a, KFoldable k, KLiftConstraints k constraints) =>
    Proxy constraints ->
    (forall child. ApplyKConstraints child constraints => Tree n child -> a) ->
    Tree k n ->
    a
foldMapKWith p f =
    withDict (kNodes (Proxy :: Proxy k)) $
    withDict (kLiftConstraintsNodeTypes (Proxy :: Proxy k) p) $
    foldMapC (pureKWith p (_ConvertK # f))

{-# INLINE traverseK_ #-}
traverseK_ ::
    (Applicative f, KFoldable k) =>
    (forall c. Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK_ f = sequenceA_ . foldMapK ((:[]) . f)

{-# INLINE traverseKWith_ #-}
traverseKWith_ ::
    forall f k constraints m.
    (Applicative f, KFoldable k, KLiftConstraints k constraints) =>
    Proxy constraints ->
    (forall c. ApplyKConstraints c constraints => Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseKWith_ p f =
    sequenceA_ . foldMapKWith @[f ()] p ((:[]) . f)
