{-# LANGUAGE NoImplicitPrelude, RankNTypes, DefaultSignatures, TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, DataKinds, TypeFamilies #-}

module AST.Class.Recursive
    ( Recursively(..), RecursiveContext, RecursiveDict, RecursiveConstraint
    , RecursiveNodes(..), recSelf, recSub
    , wrap, unwrap, wrapM, unwrapM, fold, unfold
    , foldMapRecursive
    , recursiveChildren
    ) where

import AST.Class
import AST.Class.Combinators
import AST.Class.Foldable (KFoldable, foldMapKWith)
import AST.Class.Traversable (KTraversable, traverseKWith)
import AST.Combinator.Both
import AST.Combinator.Flip
import AST.Constraint
import AST.Knot (Tree, Node, RunKnot)
import AST.Knot.Pure (Pure, _Pure)
import Control.Lens (makeLenses)
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

data RecursiveNodes a k = RecursiveNodes
    { _recSelf :: Node k a
    , _recSub :: Tree (NodeTypesOf a) (Flip RecursiveNodes (RunKnot k))
    }
makeLenses ''RecursiveNodes

instance
    Recursively HasNodes a =>
    HasNodes (RecursiveNodes a) where
    type NodeTypesOf (RecursiveNodes a) = RecursiveNodes a
    type NodesConstraint (RecursiveNodes a) = RecursiveConstraint a

instance
    Recursively HasNodes a =>
    KPointed (RecursiveNodes a) where

    {-# INLINE pureK #-}
    pureK f =
        withDict (recursive :: RecursiveDict a HasNodes) $
        withDict (hasNodes (Proxy :: Proxy a)) $
        RecursiveNodes
        { _recSelf = f
        , _recSub = pureKWith (Proxy :: Proxy '[Recursively HasNodes]) (_Flip # pureK f)
        }

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        withDict (recP p) $
        withDict (recursive :: RecursiveDict a HasNodes) $
        withDict (hasNodes (Proxy :: Proxy a)) $
        RecursiveNodes
        { _recSelf = f
        , _recSub = pureKWith (mkP p) (_Flip # pureKWithConstraint p f)
        }
        where
            recP :: Recursively c a => Proxy c -> RecursiveDict a c
            recP _ = recursive
            mkP :: Proxy c -> Proxy '[Recursively HasNodes, Recursively c]
            mkP _ = Proxy

instance
    Recursively HasNodes a =>
    KFunctor (RecursiveNodes a) where

    {-# INLINE mapC #-}
    mapC (RecursiveNodes fSelf fSub) (RecursiveNodes xSelf xSub) =
        withDict (recursive :: RecursiveDict a HasNodes) $
        withDict (hasNodes (Proxy :: Proxy a)) $
        RecursiveNodes
        { _recSelf = runMapK fSelf xSelf
        , _recSub =
            mapC
            ( mapKWith (Proxy :: Proxy '[Recursively HasNodes])
                ((_MapK #) . (\(MkFlip sf) -> _Flip %~ mapC sf)) fSub
            ) xSub
        }

instance
    Recursively HasNodes a =>
    KApply (RecursiveNodes a) where

    {-# INLINE zipK #-}
    zipK (RecursiveNodes xSelf xSub) (RecursiveNodes ySelf ySub) =
        withDict (recursive :: RecursiveDict a HasNodes) $
        withDict (hasNodes (Proxy :: Proxy a)) $
        RecursiveNodes
        { _recSelf = Both xSelf ySelf
        , _recSub =
            liftK2With (Proxy :: Proxy '[Recursively HasNodes])
            (\(MkFlip x) -> _Flip %~ zipK x) xSub ySub
        }

instance constraint Pure => Recursively constraint Pure

{-# INLINE wrapM #-}
wrapM ::
    forall m constraint expr f.
    (Monad m, Recursively constraint expr) =>
    Proxy constraint ->
    (forall child. constraint child => Tree child f -> m (Tree f child)) ->
    Tree Pure expr ->
    m (Tree f expr)
wrapM p f x =
    withDict (recursive :: RecursiveDict expr constraint) $
    x ^. _Pure
    & traverseKWith (Proxy :: Proxy '[Recursively constraint]) (wrapM p f)
    >>= f

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
    forall c0 expr a f.
    (Recursively c0 expr, Recursively KFoldable f, Monoid a) =>
    Proxy c0 ->
    (forall child g. (c0 child, Recursively KFoldable g) => Tree child g -> a) ->
    Tree expr f ->
    a
foldMapRecursive p f x =
    withDict (recursive :: RecursiveDict expr c0) $
    withDict (recursive :: RecursiveDict f KFoldable) $
    f x <>
    foldMapKWith (Proxy :: Proxy '[Recursively c0])
    (foldMapKWith (Proxy :: Proxy '[Recursively KFoldable]) (foldMapRecursive p f))
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
