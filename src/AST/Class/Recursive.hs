{-# LANGUAGE NoImplicitPrelude, RankNTypes, DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, DataKinds, TypeFamilies #-}

module AST.Class.Recursive
    ( Recursively(..), RecursiveContext, RecursiveDict, RecursiveConstraint
    , wrap, unwrap, wrapM, unwrapM, fold, unfold
    , foldMapRecursive
    , recursiveChildren
    ) where

import AST.Class (KLiftConstraint)
import AST.Class.Foldable (foldMapKWith)
import AST.Class.Traversable (KTraversable, traverseKWith)
import AST.Constraint
import AST.Knot (Tree)
import AST.Knot.Pure (Pure, _Pure)
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | `Recursively` carries a constraint to all of the descendant types
-- of an AST. As opposed to the `ChildrenConstraint` type family which
-- only carries a constraint to the direct children of an AST.
class (KTraversable expr, constraint expr) => Recursively constraint expr where
    recursive :: RecursiveDict expr constraint
    {-# INLINE recursive #-}
    -- | When an instance's constraints already imply
    -- `RecursiveContext expr constraint`, the default
    -- implementation can be used.
    default recursive ::
        RecursiveContext expr constraint => RecursiveDict expr constraint
    recursive = Dict

type RecursiveContext expr constraint =
    ( constraint expr
    , KLiftConstraint expr (Recursively constraint)
    )

type RecursiveDict expr constraint = Dict (RecursiveContext expr constraint)

class    Recursively c k => RecursiveConstraint k c
instance Recursively c k => RecursiveConstraint k c

instance KnotConstraintFunc (RecursiveConstraint k) where
    type ApplyKnotConstraint (RecursiveConstraint k) c = Recursively c k
    {-# INLINE applyKnotConstraint #-}
    applyKnotConstraint _ _ = Dict

instance constraint Pure => Recursively constraint Pure

{-# INLINE wrapM #-}
wrapM ::
    (Monad m, Recursively constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Tree child f -> m (Tree f child)) ->
    Tree Pure expr ->
    m (Tree f expr)
wrapM p f x =
    x ^. _Pure & recursiveChildren p (wrapM p f) >>= f

{-# INLINE unwrapM #-}
unwrapM ::
    (Monad m, Recursively constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Tree f child -> m (Tree child f)) ->
    Tree f expr ->
    m (Tree Pure expr)
unwrapM p f x =
    f x >>= recursiveChildren p (unwrapM p f) <&> (_Pure #)

{-# INLINE wrap #-}
wrap ::
    Recursively constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree child f -> Tree f child) ->
    Tree Pure expr ->
    Tree f expr
wrap p f = runIdentity . wrapM p (Identity . f)

{-# INLINE unwrap #-}
unwrap ::
    Recursively constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree f child -> Tree child f) ->
    Tree f expr ->
    Tree Pure expr
unwrap p f = runIdentity . unwrapM p (Identity . f)

-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
{-# INLINE fold #-}
fold ::
    Recursively constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree child (Const a) -> a) ->
    Tree Pure expr ->
    a
fold p f = getConst . wrap p (Const . f)

-- | Build/load a tree from a seed value.
-- TODO: Is this an "ana-morphism"?
{-# INLINE unfold #-}
unfold ::
    Recursively constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => a -> Tree child (Const a)) ->
    a ->
    Tree Pure expr
unfold p f = unwrap p (f . getConst) . Const

{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall c0 c1 expr a f.
    (Recursively c0 expr, Recursively c1 f, Monoid a) =>
    Proxy c0 ->
    Proxy c1 ->
    (forall child g. (c0 child, Recursively c1 g) => Tree child g -> a) ->
    Tree expr f ->
    a
foldMapRecursive p0 p1 f x =
    withDict (recursive :: RecursiveDict expr c0) $
    withDict (recursive :: RecursiveDict f c1) $
    f x <>
    foldMapKWith (Proxy :: Proxy '[Recursively c0])
    (foldMapKWith (Proxy :: Proxy '[Recursively c1]) (foldMapRecursive p0 p1 f))
    x

{-# INLINE recursiveChildren #-}
recursiveChildren ::
    forall constraint expr n m f.
    (Applicative f, Recursively constraint expr) =>
    Proxy constraint ->
    (forall child. Recursively constraint child => Tree n child -> f (Tree m child)) ->
    Tree expr n -> f (Tree expr m)
recursiveChildren _ f x =
    withDict (recursive :: RecursiveDict expr constraint) $
    traverseKWith (Proxy :: Proxy '[Recursively constraint]) f x
