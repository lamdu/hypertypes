{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, RankNTypes, StandaloneDeriving, TypeOperators #-}

module AST.Infer.Term
    ( ITerm(..), iVal, iRes, iAnn
    , InferChildConstraints, InferChildDeps
    , iType, iScope, iAnnotations
    ) where

import AST
import AST.Class
import AST.Class.Foldable
import AST.Class.Traversable
import AST.Combinator.Flip (Flip(..), _Flip)
import AST.Infer.Result
import Control.Lens (Traversal, Iso, Lens', makeLenses, makePrisms, from, iso)
import Control.Lens.Operators
import Data.Constraint
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
data ITerm a v e = ITerm
    { _iAnn :: a
    , _iRes :: {-# UNPACK #-} !(Tree (IResult (RunKnot e)) v)
    , _iVal :: Node e (ITerm a v)
    }
makeLenses ''ITerm

type InferChildDeps c ast =
    ( c (TypeOf ast)
    , KTraversable ast
    , KTraversable (ScopeOf ast)
    , NodesConstraint (ScopeOf ast) $ c
    )
class    InferChildDeps c ast => InferChildConstraints c ast
instance InferChildDeps c ast => InferChildConstraints c ast

data InferConstraint :: (Knot -> Type) -> ((Knot -> Type) -> Constraint) ~> Constraint

type instance Apply (InferConstraint k) c = Recursively (InferChildConstraints c) k

newtype IResultNodeTypes k e =
    MkIResultNodeTypes { runIResultNodeTypes :: NodeTypesOf (IResult (RunKnot e)) k }

_IResultNodeTypes ::
    Iso (Tree (IResultNodeTypes k0) e0)
        (Tree (IResultNodeTypes k1) e1)
        (NodeTypesOf (IResult e0) k0)
        (NodeTypesOf (IResult e1) k1)
_IResultNodeTypes = iso runIResultNodeTypes MkIResultNodeTypes

newtype ITermTypes e k =
    ITermTypes (Tree (RecursiveNodes e) (IResultNodeTypes k))
makePrisms ''ITermTypes

instance
    ( Recursively KNodes e
    , Recursively (InferChildConstraints KNodes) e
    ) =>
    KPointed (ITermTypes e) where

    {-# INLINE pureK #-}
    pureK f =
        pureKWithConstraint (Proxy :: Proxy (InferChildConstraints KNodes)) (g f)
        & ITermTypes
        where
            g ::
                forall child n.
                KNodes (ScopeOf child) =>
                (forall c. Tree n c) ->
                Tree (IResultNodeTypes ('Knot n)) child
            g f1 =
                withDict (kNodes (Proxy :: Proxy (ScopeOf child))) $
                _IResultNodeTypes # pureK f1

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        pureKWith (makeP p) (g p f)
        & ITermTypes
        where
            makeP ::
                Proxy c ->
                Proxy '[InferChildConstraints c, InferChildConstraints KNodes]
            makeP _ = Proxy
            g ::
                forall child n constraint.
                ( KNodes (ScopeOf child)
                , constraint (TypeOf child)
                , NodesConstraint (ScopeOf child) $ constraint
                ) =>
                Proxy constraint ->
                (forall c. constraint c => Tree n c) ->
                Tree (IResultNodeTypes ('Knot n)) child
            g p1 f1 =
                withDict (kNodes (Proxy :: Proxy (ScopeOf child))) $
                _IResultNodeTypes # pureKWithConstraint p1 f1

instance
    ( Recursively KNodes e
    , Recursively (InferChildConstraints KNodes) e
    ) =>
    KFunctor (ITermTypes e) where

    {-# INLINE mapC #-}
    mapC (ITermTypes (RecursiveNodes (MkIResultNodeTypes mapTop) mapSub)) =
        _ITermTypes %~
        \(RecursiveNodes t s) ->
        RecursiveNodes
        { _recSelf =
            withDict (kNodes (Proxy :: Proxy (ScopeOf e))) $
            t & _IResultNodeTypes %~ mapC mapTop
        , _recSub =
            withDict (kNodes (Proxy :: Proxy e)) $
            withDict (recursive :: RecursiveDict e KNodes) $
            withDict (recursive :: RecursiveDict e (InferChildConstraints KNodes)) $
            mapC
            ( mapKWith
                (Proxy ::
                    Proxy '[Recursively KNodes, Recursively (InferChildConstraints KNodes)])
                ( \(MkFlip f) ->
                    _Flip %~
                    mapC
                    ( mapKWith (Proxy :: Proxy '[InferChildConstraints KNodes]) g f
                    ) & MkMapK
                ) mapSub
            ) s
        }
        where
            g ::
                forall child n m.
                KNodes (ScopeOf child) =>
                Tree (IResultNodeTypes ('Knot (MapK m n))) child ->
                Tree (MapK (IResultNodeTypes ('Knot m)) (IResultNodeTypes ('Knot n))) child
            g (MkIResultNodeTypes i) =
                withDict (kNodes (Proxy :: Proxy (ScopeOf child))) $
                _IResultNodeTypes %~ mapC i & MkMapK

instance
    ( Recursively KNodes e
    , Recursively (InferChildConstraints KNodes) e
    ) =>
    KApply (ITermTypes e) where

    {-# INLINE zipK #-}
    zipK (ITermTypes x) =
        _ITermTypes %~
        liftK2With (Proxy :: Proxy '[InferChildConstraints KNodes]) f x
        where
            f ::
                forall a b c.
                KNodes (ScopeOf c) =>
                Tree (IResultNodeTypes ('Knot a)) c ->
                Tree (IResultNodeTypes ('Knot b)) c ->
                Tree (IResultNodeTypes ('Knot (Product a b))) c
            f (MkIResultNodeTypes x1) =
                withDict (kNodes (Proxy :: Proxy (ScopeOf c))) $
                _IResultNodeTypes %~ zipK x1

instance
    ( Recursively KNodes e
    , Recursively (InferChildConstraints KNodes) e
    ) =>
    KNodes (ITermTypes e) where

    type NodeTypesOf (ITermTypes e) = ITermTypes e
    type NodesConstraint (ITermTypes e) = InferConstraint e

instance
    ( Recursively KNodes e
    , Recursively (InferChildConstraints KNodes) e
    ) =>
    KNodes (Flip (ITerm a) e) where

    type NodeTypesOf (Flip (ITerm a) e) = ITermTypes e

instance
    ( Recursively (InferChildConstraints KNodes) e
    , Recursively KNodes e
    ) =>
    KFunctor (Flip (ITerm a) e) where

    {-# INLINE mapC #-}
    mapC (ITermTypes (RecursiveNodes (MkIResultNodeTypes ft) fs)) =
        withDict (kNodes (Proxy :: Proxy e)) $
        withDict (recursive :: RecursiveDict e KNodes) $
        withDict (recursive :: RecursiveDict e (InferChildConstraints KNodes)) $
        _Flip %~
        \(ITerm a r x) ->
        ITerm a
        (mapC ft r)
        (mapC
            ( mapKWith (Proxy :: Proxy '[Recursively KNodes, Recursively (InferChildConstraints KNodes)])
                (\(MkFlip f) -> from _Flip %~ mapC (ITermTypes f) & MkMapK) fs
            ) x
        )

instance
    ( KFoldable e
    , KFoldable (ScopeOf e)
    , Recursively KNodes e
    , Recursively (InferChildConstraints KNodes) e
    ) =>
    KFoldable (Flip (ITerm a) e) where
    {-# INLINE foldMapC #-}
    foldMapC (ITermTypes (RecursiveNodes (MkIResultNodeTypes ft) fs)) (MkFlip (ITerm _ r x)) =
        withDict (kNodes (Proxy :: Proxy e)) $
        withDict (recursive :: RecursiveDict e KNodes) $
        withDict (recursive :: RecursiveDict e (InferChildConstraints KNodes)) $
        foldMapC ft r <>
        foldMapC
        ( mapKWith
            (Proxy ::
                Proxy '[Recursively KNodes, Recursively (InferChildConstraints KNodes)])
            (\(MkFlip f) -> foldMapC (ITermTypes f) . (_Flip #) & MkConvertK) fs
        ) x

instance
    ( Recursively KNodes e
    , Recursively (InferChildConstraints KNodes) e
    ) =>
    KTraversable (Flip (ITerm a) e) where

    {-# INLINE sequenceC #-}
    sequenceC =
        withDict (recursive :: RecursiveDict e KNodes) $
        withDict (recursive :: RecursiveDict e (InferChildConstraints KNodes)) $
        _Flip $
        \(ITerm a r x) ->
        ITerm a
        <$> traverseK runContainedK r
        <*> traverseKWith
            (Proxy :: Proxy '[Recursively KNodes, Recursively (InferChildConstraints KNodes)])
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

deriving instance (Show a, Show (Node e (ITerm a v)), Show (Tree (IResult (RunKnot e)) v)) => Show (ITerm a v e)
