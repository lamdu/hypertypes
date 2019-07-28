{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes, StandaloneDeriving #-}

module AST.Infer.Term
    ( TypeOf, ScopeOf
    , IResult(..), irType, irScope
    , ITerm(..), iVal, iRes, iAnn
    , InferChildConstraints, InferChildDeps
    , iType, iScope, iAnnotations
    ) where

import AST
import AST.Class
import AST.Class.Foldable
import AST.Class.Traversable
import AST.Constraint
import AST.Combinator.Both
import AST.Combinator.Flip (Flip(..), _Flip)
import Control.Lens (Traversal, Lens', makeLenses, makePrisms, from)
import Control.Lens.Operators
import Data.Constraint
import Data.Proxy (Proxy(..))

import Prelude.Compat

type family TypeOf (t :: Knot -> *) :: Knot -> *
type family ScopeOf (t :: Knot -> *) :: Knot -> *

data IResult e v = IResult
    { _irType :: Node v (TypeOf e)
    , _irScope :: ScopeOf e v
    }
makeLenses ''IResult

data IResultNodeTypes e k = IResultNodeTypes
    { _ircType :: Node k (TypeOf e)
    , _ircScope :: NodeTypesOf (ScopeOf e) k
    }

instance
    HasNodes (ScopeOf e) =>
    HasNodes (IResultNodeTypes e) where

    type NodeTypesOf (IResultNodeTypes e) = IResultNodeTypes e
    type NodesConstraint (IResultNodeTypes e) =
        ConcatKnotConstraints '[KnotsConstraint '[TypeOf e], NodesConstraint (ScopeOf e)]

instance
    HasNodes (ScopeOf e) =>
    KPointed (IResultNodeTypes e) where

    {-# INLINE pureK #-}
    pureK f =
        withDict (hasNodes (Proxy :: Proxy (ScopeOf e))) $
        IResultNodeTypes f (pureK f)

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        withDict (hasNodes (Proxy :: Proxy (ScopeOf e))) $
        IResultNodeTypes f (pureKWithConstraint p f)

instance
    HasNodes (ScopeOf e) =>
    KFunctor (IResultNodeTypes e) where

    {-# INLINE mapC #-}
    mapC (IResultNodeTypes (MkMapK mapType) mapScope) (IResultNodeTypes t s) =
        IResultNodeTypes
        { _ircType = mapType t
        , _ircScope =
            withDict (hasNodes (Proxy :: Proxy (ScopeOf e))) $
            mapC mapScope s
        }

instance
    HasNodes (ScopeOf e) =>
    KApply (IResultNodeTypes e) where

    {-# INLINE zipK #-}
    zipK (IResultNodeTypes t0 s0) (IResultNodeTypes t1 s1) =
        withDict (hasNodes (Proxy :: Proxy (ScopeOf e))) $
        IResultNodeTypes (Both t0 t1) (zipK s0 s1)

instance
    HasNodes (ScopeOf e) =>
    HasNodes (IResult e) where

    type NodeTypesOf (IResult e) = IResultNodeTypes e
    type NodesConstraint (IResult e) = NodesConstraint (IResultNodeTypes e)

makeKApplicativeBases ''IResult
makeKTraversableAndFoldable ''IResult

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
--
-- See also `AST.Class.Infer.Inferred.Inferred`, a newtype wrapper
-- knotted by `v` whose children are the types.
data ITerm a v e = ITerm
    { _iAnn :: a
    , _iRes :: {-# UNPACK #-} !(Tree (IResult (RunKnot e)) v)
    , _iVal :: Node e (ITerm a v)
    }
makeLenses ''ITerm

-- TODO: This should get a list of constraints
type InferChildDeps c ast =
    ( c (TypeOf ast)
    , KTraversable ast
    , KTraversable (ScopeOf ast)
    , KLiftConstraint (ScopeOf ast) c
    )
class    InferChildDeps c ast => InferChildConstraints c ast
instance InferChildDeps c ast => InferChildConstraints c ast

class    Recursively (InferChildConstraints c) k => InferConstraint k c
instance Recursively (InferChildConstraints c) k => InferConstraint k c

instance KnotConstraintFunc (InferConstraint k) where
    type ApplyKnotConstraint (InferConstraint k) c = Recursively (InferChildConstraints c) k
    {-# INLINE applyKnotConstraint #-}
    applyKnotConstraint _ _ = Dict

newtype ITermTypes e k =
    ITermTypes (Tree (RecursiveNodes e) (Flip IResultNodeTypes (RunKnot k)))
makePrisms ''ITermTypes

instance
    ( Recursively HasNodes e
    , Recursively (InferChildConstraints HasNodes) e
    ) =>
    KPointed (ITermTypes e) where

    {-# INLINE pureK #-}
    pureK f =
        pureKWithConstraint (Proxy :: Proxy (InferChildConstraints HasNodes))
        (_Flip # pureK f)
        & ITermTypes

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        pureKWith (makeP p)
        (_Flip # pureKWithConstraint p f)
        & ITermTypes
        where
            makeP ::
                Proxy c ->
                Proxy '[InferChildConstraints c, InferChildConstraints HasNodes]
            makeP _ = Proxy

instance
    ( Recursively HasNodes e
    , Recursively (InferChildConstraints HasNodes) e
    ) =>
    KFunctor (ITermTypes e) where

    {-# INLINE mapC #-}
    mapC (ITermTypes (RecursiveNodes (MkFlip mapTop) mapSub)) =
        _ITermTypes %~
        \(RecursiveNodes t s) ->
        RecursiveNodes
        { _recSelf = t & _Flip %~ mapC mapTop
        , _recSub =
            withDict (hasNodes (Proxy :: Proxy e)) $
            withDict (recursive :: RecursiveDict e HasNodes) $
            withDict (recursive :: RecursiveDict e (InferChildConstraints HasNodes)) $
            mapC
            ( mapKWith
                (Proxy ::
                    Proxy '[Recursively HasNodes, Recursively (InferChildConstraints HasNodes)])
                ( \(MkFlip f) ->
                    _Flip %~
                    mapC
                    ( mapKWith (Proxy :: Proxy '[InferChildConstraints HasNodes])
                        ( \(MkFlip i) ->
                            _Flip %~ mapC i
                            & MkMapK
                        ) f
                    ) & MkMapK
                ) mapSub
            ) s
        }

instance
    ( Recursively HasNodes e
    , Recursively (InferChildConstraints HasNodes) e
    ) =>
    KApply (ITermTypes e) where

    {-# INLINE zipK #-}
    zipK (ITermTypes x) =
        _ITermTypes %~
        liftK2With (Proxy :: Proxy '[InferChildConstraints HasNodes])
        (\(MkFlip x0) -> _Flip %~ zipK x0) x

instance
    ( Recursively HasNodes e
    , Recursively (InferChildConstraints HasNodes) e
    ) =>
    HasNodes (ITermTypes e) where

    type NodeTypesOf (ITermTypes e) = ITermTypes e
    type NodesConstraint (ITermTypes e) = InferConstraint e

    {-# INLINE hasNodes #-}
    hasNodes _ = Dict

instance
    ( Recursively HasNodes e
    , Recursively (InferChildConstraints HasNodes) e
    ) =>
    HasNodes (Flip (ITerm a) e) where

    type NodeTypesOf (Flip (ITerm a) e) = ITermTypes e
    type NodesConstraint (Flip (ITerm a) e) = NodesConstraint (ITermTypes e)

instance
    ( Recursively (InferChildConstraints HasNodes) e
    , Recursively HasNodes e
    ) =>
    KFunctor (Flip (ITerm a) e) where

    {-# INLINE mapC #-}
    mapC (ITermTypes (RecursiveNodes (MkFlip ft) fs)) =
        withDict (hasNodes (Proxy :: Proxy e)) $
        withDict (recursive :: RecursiveDict e HasNodes) $
        withDict (recursive :: RecursiveDict e (InferChildConstraints HasNodes)) $
        _Flip %~
        \(ITerm a r x) ->
        ITerm a
        (mapC ft r)
        (mapC
            ( mapKWith (Proxy :: Proxy '[Recursively HasNodes, Recursively (InferChildConstraints HasNodes)])
                (\(MkFlip f) -> from _Flip %~ mapC (ITermTypes f) & MkMapK) fs
            ) x
        )

instance
    ( KFoldable e
    , KFoldable (ScopeOf e)
    , Recursively HasNodes e
    , Recursively (InferChildConstraints HasNodes) e
    ) =>
    KFoldable (Flip (ITerm a) e) where
    {-# INLINE foldMapC #-}
    foldMapC (ITermTypes (RecursiveNodes (MkFlip ft) fs)) (MkFlip (ITerm _ r x)) =
        withDict (hasNodes (Proxy :: Proxy e)) $
        withDict (recursive :: RecursiveDict e HasNodes) $
        withDict (recursive :: RecursiveDict e (InferChildConstraints HasNodes)) $
        foldMapC ft r <>
        foldMapC
        ( mapKWith
            (Proxy ::
                Proxy '[Recursively HasNodes, Recursively (InferChildConstraints HasNodes)])
            (\(MkFlip f) -> foldMapC (ITermTypes f) . (_Flip #) & MkConvertK) fs
        ) x

instance
    ( Recursively HasNodes e
    , Recursively (InferChildConstraints HasNodes) e
    ) =>
    KTraversable (Flip (ITerm a) e) where

    {-# INLINE sequenceC #-}
    sequenceC =
        withDict (recursive :: RecursiveDict e HasNodes) $
        withDict (recursive :: RecursiveDict e (InferChildConstraints HasNodes)) $
        _Flip $
        \(ITerm a r x) ->
        ITerm a
        <$> traverseK runContainedK r
        <*> traverseKWith
            (Proxy :: Proxy '[Recursively HasNodes, Recursively (InferChildConstraints HasNodes)])
            (from _Flip sequenceC) x

iType :: Lens' (ITerm a v e) (Tree v (TypeOf (RunKnot e)))
iType = iRes . irType

iScope :: Lens' (ITerm a v e) (Tree (ScopeOf (RunKnot e)) v)
iScope = iRes . irScope

iAnnotations ::
    forall e a b v.
    Recursively KTraversable e =>
    Traversal
    (Tree (ITerm a v) e)
    (Tree (ITerm b v) e)
    a b
iAnnotations f (ITerm pl r x) =
    withDict (recursive :: RecursiveDict e KTraversable) $
    ITerm
    <$> f pl
    <*> pure r
    <*> traverseKWith (Proxy :: Proxy '[Recursively KTraversable]) (iAnnotations f) x

deriving instance (Show (Tree v (TypeOf e)), Show (Tree (ScopeOf e) v)) => Show (Tree (IResult e) v)
deriving instance (Show a, Show (Node e (ITerm a v)), Show (Tree (IResult (RunKnot e)) v)) => Show (ITerm a v e)
