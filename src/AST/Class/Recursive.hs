{-# LANGUAGE NoImplicitPrelude, RankNTypes, DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module AST.Class.Recursive
    ( Recursive(..), RecursiveConstraint, RecursiveDict
    , wrap, unwrap, wrapM, unwrapM, fold, unfold
    , foldMapRecursive
    ) where

import AST.Class.Children (Children(..), foldMapChildren)
import AST.Knot (Tree)
import AST.Knot.Pure (Pure(..))
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | `Recursive` carries a constraint to all of the descendant types
-- of an AST. As opposed to the `ChildrenConstraint` type family which
-- only carries a constraint to the direct children of an AST.
class (Children expr, constraint expr) => Recursive constraint expr where
    recursive :: RecursiveDict constraint expr
    -- | When an instance's constraints already imply
    -- `RecursiveConstraint expr constraint`, the default
    -- implementation can be used.
    default recursive ::
        RecursiveConstraint expr constraint => RecursiveDict constraint expr
    recursive = Dict

type RecursiveConstraint expr constraint =
    ( constraint expr
    , ChildrenConstraint expr (Recursive constraint)
    )

type RecursiveDict constraint expr = Dict (RecursiveConstraint expr constraint)

instance constraint Pure => Recursive constraint Pure
instance constraint (Const a) => Recursive constraint (Const a)

wrapM ::
    forall constraint expr f m.
    (Monad m, Recursive constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Tree child f -> m (Tree f child)) ->
    Tree Pure expr ->
    m (Tree f expr)
wrapM p f (Pure x) =
    withDict (recursive :: RecursiveDict constraint expr) $
    children (Proxy :: Proxy (Recursive constraint)) (wrapM p f) x >>= f

unwrapM ::
    forall constraint expr f m.
    (Monad m, Recursive constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Tree f child -> m (Tree child f)) ->
    Tree f expr ->
    m (Tree Pure expr)
unwrapM p f x =
    withDict (recursive :: RecursiveDict constraint expr) $
    f x >>= children (Proxy :: Proxy (Recursive constraint)) (unwrapM p f) <&> Pure

wrap ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree child f -> Tree f child) ->
    Tree Pure expr ->
    Tree f expr
wrap p f = runIdentity . wrapM p (Identity . f)

unwrap ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree f child -> Tree child f) ->
    Tree f expr ->
    Tree Pure expr
unwrap p f = runIdentity . unwrapM p (Identity . f)

-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
fold ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree child (Const a) -> a) ->
    Tree Pure expr ->
    a
fold p f = getConst . wrap p (Const . f)

-- | Build/load a tree from a seed value.
-- TODO: Is this an "ana-morphism"?
unfold ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => a -> Tree child (Const a)) ->
    a ->
    Tree Pure expr
unfold p f = unwrap p (f . getConst) . Const

foldMapRecursive ::
    forall constraint expr a f.
    (Recursive constraint expr, Recursive Children f, Monoid a) =>
    Proxy constraint ->
    (forall child g. (constraint child, Recursive Children g) => Tree child g -> a) ->
    Tree expr f ->
    a
foldMapRecursive p f x =
    withDict (recursive :: RecursiveDict constraint expr) $
    withDict (recursive :: RecursiveDict Children f) $
    f x <>
    foldMapChildren (Proxy :: Proxy (Recursive constraint))
    (foldMapChildren (Proxy :: Proxy (Recursive Children)) (foldMapRecursive p f))
    x
