{-# LANGUAGE NoImplicitPrelude, RankNTypes, DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, DataKinds, TypeFamilies #-}

module AST.Class.Recursive
    ( Recursive(..), RecursiveConstraint, RecursiveDict
    , wrap, unwrap, wrapM, unwrapM, fold, unfold
    , foldMapRecursive
    , recursiveChildren, recursiveOverChildren, recursiveChildren_
    ) where

import AST.Class.Children (Children(..))
import AST.Class.Combinators
import AST.Class.HasChildrenTypes
import AST.Class.Pointed (KPointed(..))
import AST.Class.Traversable (KTraversable)
import AST.Knot (Tree, ChildrenTypesOf)
import AST.Knot.Pure (Pure, _Pure)
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | `Recursive` carries a constraint to all of the descendant types
-- of an AST. As opposed to the `ChildrenConstraint` type family which
-- only carries a constraint to the direct children of an AST.
class (KTraversable expr, HasChildrenTypes expr, Children expr, constraint expr) => Recursive constraint expr where
    recursive :: RecursiveDict constraint expr
    {-# INLINE recursive #-}
    -- | When an instance's constraints already imply
    -- `RecursiveConstraint expr constraint`, the default
    -- implementation can be used.
    default recursive ::
        RecursiveConstraint expr constraint => RecursiveDict constraint expr
    recursive = Dict

type RecursiveConstraint expr constraint =
    ( constraint expr
    , ChildrenConstraint expr (Recursive constraint)
    , KLiftConstraint (ChildrenTypesOf expr) (Recursive constraint)
    )

type RecursiveDict constraint expr = Dict (RecursiveConstraint expr constraint)

instance constraint Pure => Recursive constraint Pure
instance constraint (Const a) => Recursive constraint (Const a)

{-# INLINE wrapM #-}
wrapM ::
    (Monad m, Recursive constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Tree child f -> m (Tree f child)) ->
    Tree Pure expr ->
    m (Tree f expr)
wrapM p f x =
    x ^. _Pure & recursiveChildren p (wrapM p f) >>= f

{-# INLINE unwrapM #-}
unwrapM ::
    (Monad m, Recursive constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Tree f child -> m (Tree child f)) ->
    Tree f expr ->
    m (Tree Pure expr)
unwrapM p f x =
    f x >>= recursiveChildren p (unwrapM p f) <&> (_Pure #)

{-# INLINE wrap #-}
wrap ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree child f -> Tree f child) ->
    Tree Pure expr ->
    Tree f expr
wrap p f = runIdentity . wrapM p (Identity . f)

{-# INLINE unwrap #-}
unwrap ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree f child -> Tree child f) ->
    Tree f expr ->
    Tree Pure expr
unwrap p f = runIdentity . unwrapM p (Identity . f)

-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
{-# INLINE fold #-}
fold ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree child (Const a) -> a) ->
    Tree Pure expr ->
    a
fold p f = getConst . wrap p (Const . f)

-- | Build/load a tree from a seed value.
-- TODO: Is this an "ana-morphism"?
{-# INLINE unfold #-}
unfold ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => a -> Tree child (Const a)) ->
    a ->
    Tree Pure expr
unfold p f = unwrap p (f . getConst) . Const

{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall c0 c1 expr a f.
    (Recursive c0 expr, Recursive c1 f, Monoid a) =>
    Proxy c0 ->
    Proxy c1 ->
    (forall child g. (c0 child, Recursive c1 g) => Tree child g -> a) ->
    Tree expr f ->
    a
foldMapRecursive p0 p1 f x =
    withDict (recursive :: RecursiveDict c0 expr) $
    withDict (recursive :: RecursiveDict c1 f) $
    withDict (hasChildrenTypes (Proxy :: Proxy expr)) $
    withDict (hasChildrenTypes (Proxy :: Proxy f)) $
    f x <>
    foldMapKWith (Proxy :: Proxy '[Recursive c0])
    (foldMapKWith (Proxy :: Proxy '[Recursive c1]) (foldMapRecursive p0 p1 f))
    x

{-# INLINE recursiveChildren #-}
recursiveChildren ::
    forall constraint expr n m f.
    (Applicative f, Recursive constraint expr) =>
    Proxy constraint ->
    (forall child. Recursive constraint child => Tree n child -> f (Tree m child)) ->
    Tree expr n -> f (Tree expr m)
recursiveChildren _ f x =
    withDict (recursive :: RecursiveDict constraint expr) $
    children (Proxy :: Proxy (Recursive constraint)) f x

{-# INLINE recursiveChildren_ #-}
recursiveChildren_ ::
    forall constraint expr n f.
    (Applicative f, Recursive constraint expr) =>
    Proxy constraint ->
    (forall child. Recursive constraint child => Tree n child -> f ()) ->
    Tree expr n -> f ()
recursiveChildren_ _ f x =
    withDict (recursive :: RecursiveDict constraint expr) $
    withDict (hasChildrenTypes (Proxy :: Proxy expr)) $
    traverseKWith_ (Proxy :: Proxy '[Recursive constraint]) f x

{-# INLINE recursiveOverChildren #-}
recursiveOverChildren ::
    forall constraint expr n m.
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. Recursive constraint child => Tree n child -> Tree m child) ->
    Tree expr n -> Tree expr m
recursiveOverChildren _ f x =
    withDict (recursive :: RecursiveDict constraint expr) $
    withDict (hasChildrenTypes (Proxy :: Proxy expr)) $
    mapKWith (Proxy :: Proxy '[Recursive constraint]) f x
