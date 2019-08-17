{-# LANGUAGE TemplateHaskell, FlexibleContexts, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}

module AST.Infer.Term
    ( ITerm(..), iVal, iRes, iAnn
    , iAnnotations
    ) where

import AST
import AST.Class
import AST.Class.Combinators
import AST.Class.Foldable
import AST.Class.Infer
import AST.Class.Recursive
import AST.Class.Traversable
import AST.Combinator.Flip (Flip(..), _Flip)
import Control.Lens (Traversal, Iso, makeLenses, makePrisms, from, iso)
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
    , _iRes :: !(Tree (InferOf (RunKnot e)) v)
    , _iVal :: Node e (ITerm a v)
    }
makeLenses ''ITerm

data InferConstraint :: (Knot -> Type) -> ((Knot -> Type) -> Constraint) ~> Constraint

type instance Apply (InferConstraint k) c =
    Recursively (InferOfConstraint (KLiftConstraint c)) k

newtype IResultNodeTypes k e =
    MkIResultNodeTypes { runIResultNodeTypes :: NodeTypesOf (InferOf (RunKnot e)) k }

_IResultNodeTypes ::
    Iso (Tree (IResultNodeTypes k0) e0)
        (Tree (IResultNodeTypes k1) e1)
        (NodeTypesOf (InferOf e0) k0)
        (NodeTypesOf (InferOf e1) k1)
_IResultNodeTypes = iso runIResultNodeTypes MkIResultNodeTypes

newtype ITermTypes e k =
    ITermTypes (Tree (RecursiveNodes e) (IResultNodeTypes k))
makePrisms ''ITermTypes

instance
    ( Recursively KNodes e
    , Recursively (InferOfConstraint KNodes) e
    ) =>
    KNodes (ITermTypes e) where

    type NodeTypesOf (ITermTypes e) = ITermTypes e
    type NodesConstraint (ITermTypes e) = InferConstraint e

instance
    ( Recursively KNodes e
    , Recursively (InferOfConstraint KNodes) e
    ) =>
    KPointed (ITermTypes e) where

    {-# INLINE pureK #-}
    pureK f =
        pureKWithConstraint (Proxy @(InferOfConstraint KNodes)) (g f)
        & ITermTypes
        where
            g ::
                forall child n.
                KNodes (InferOf child) =>
                (forall c. Tree n c) ->
                Tree (IResultNodeTypes ('Knot n)) child
            g f1 =
                withDict (kNodes (Proxy @(InferOf child))) $
                _IResultNodeTypes # pureK f1

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        pureKWith (makeP p) (g p f)
        & ITermTypes
        where
            makeP ::
                Proxy c ->
                Proxy '[InferOfConstraint KNodes, InferOfConstraint (KLiftConstraint c)]
            makeP _ = Proxy
            g ::
                forall child n constraint.
                ( KNodes (InferOf child)
                , NodesConstraint (InferOf child) $ constraint
                ) =>
                Proxy constraint ->
                (forall c. constraint c => Tree n c) ->
                Tree (IResultNodeTypes ('Knot n)) child
            g p1 f1 =
                withDict (kNodes (Proxy @(InferOf child))) $
                _IResultNodeTypes # pureKWithConstraint p1 f1

instance
    ( Recursively KNodes e
    , Recursively (InferOfConstraint KNodes) e
    ) =>
    KFunctor (ITermTypes e) where

    {-# INLINE mapC #-}
    mapC (ITermTypes (RecursiveNodes (MkIResultNodeTypes mapTop) mapSub)) =
        _ITermTypes %~
        \(RecursiveNodes t s) ->
        RecursiveNodes
        { _recSelf =
            withDict (kNodes (Proxy @(InferOf e))) $
            t & _IResultNodeTypes %~ mapC mapTop
        , _recSub =
            withDict (kNodes (Proxy @e)) $
            withDict (recursive @KNodes @e) $
            withDict (recursive @(InferOfConstraint KNodes) @e) $
            mapC
            ( mapKWith
                (Proxy ::
                    Proxy '[Recursively KNodes, Recursively (InferOfConstraint KNodes)])
                ( \(MkFlip f) ->
                    _Flip %~
                    mapC
                    ( mapKWithConstraint (Proxy @(InferOfConstraint KNodes)) g f
                    ) & MkMapK
                ) mapSub
            ) s
        }
        where
            g ::
                forall child n m.
                KNodes (InferOf child) =>
                Tree (IResultNodeTypes ('Knot (MapK m n))) child ->
                Tree (MapK (IResultNodeTypes ('Knot m)) (IResultNodeTypes ('Knot n))) child
            g (MkIResultNodeTypes i) =
                withDict (kNodes (Proxy @(InferOf child))) $
                _IResultNodeTypes %~ mapC i & MkMapK

instance
    ( Recursively KNodes e
    , Recursively (InferOfConstraint KNodes) e
    ) =>
    KApply (ITermTypes e) where

    {-# INLINE zipK #-}
    zipK (ITermTypes x) =
        _ITermTypes %~
        liftK2With (Proxy @'[InferOfConstraint KNodes]) f x
        where
            f ::
                forall a b c.
                KNodes (InferOf c) =>
                Tree (IResultNodeTypes ('Knot a)) c ->
                Tree (IResultNodeTypes ('Knot b)) c ->
                Tree (IResultNodeTypes ('Knot (Product a b))) c
            f (MkIResultNodeTypes x1) =
                withDict (kNodes (Proxy @(InferOf c))) $
                _IResultNodeTypes %~ zipK x1

instance
    ( Recursively KNodes e
    , Recursively (InferOfConstraint KNodes) e
    ) =>
    KNodes (Flip (ITerm a) e) where

    type NodeTypesOf (Flip (ITerm a) e) = ITermTypes e

instance
    ( RFunctor e
    , Inferrable e
    , Recursively (InferOfConstraint KNodes) e
    ) =>
    KFunctor (Flip (ITerm a) e) where

    {-# INLINE mapC #-}
    mapC (ITermTypes (RecursiveNodes (MkIResultNodeTypes ft) fs)) =
        withDict (traversableInferOf (Proxy @e)) $
        withDict (inferrableRecursive (Proxy @e)) $
        withDict (kNodes (Proxy @e)) $
        withDict (recursiveKFunctor (Proxy @e)) $
        withDict (recursive @(InferOfConstraint KNodes) @e) $
        _Flip %~
        \(ITerm a r x) ->
        ITerm a
        (mapC ft r)
        (mapC
            ( mapKWith
                (Proxy ::
                    Proxy
                    '[RFunctor
                    , Inferrable
                    , Recursively (InferOfConstraint KNodes)
                    ])
                (\(MkFlip f) -> from _Flip %~ mapC (ITermTypes f) & MkMapK) fs
            ) x
        )

instance
    ( RFoldable e
    , Inferrable e
    , Recursively (InferOfConstraint KNodes) e
    ) =>
    KFoldable (Flip (ITerm a) e) where
    {-# INLINE foldMapC #-}
    foldMapC (ITermTypes (RecursiveNodes (MkIResultNodeTypes ft) fs)) (MkFlip (ITerm _ r x)) =
        withDict (traversableInferOf (Proxy @e)) $
        withDict (inferrableRecursive (Proxy @e)) $
        withDict (kNodes (Proxy @e)) $
        withDict (recursiveKFoldable (Proxy @e)) $
        withDict (recursive @(InferOfConstraint KNodes) @e) $
        foldMapC ft r <>
        foldMapC
        ( mapKWith
            (Proxy ::
                Proxy
                '[RFoldable
                , Inferrable
                , Recursively (InferOfConstraint KNodes)
                ])
            (\(MkFlip f) -> foldMapC (ITermTypes f) . (_Flip #) & MkConvertK) fs
        ) x

instance
    ( RTraversable e
    , Inferrable e
    , Recursively (InferOfConstraint KNodes) e
    ) =>
    KTraversable (Flip (ITerm a) e) where

    {-# INLINE sequenceC #-}
    sequenceC =
        withDict (traversableInferOf (Proxy @e)) $
        withDict (inferrableRecursive (Proxy @e)) $
        withDict (recursiveKTraversable (Proxy @e)) $
        withDict (recursive @(InferOfConstraint KNodes) @e) $
        _Flip $
        \(ITerm a r x) ->
        ITerm a
        <$> traverseK runContainedK r
        <*> traverseKWith
            (Proxy ::
                Proxy
                '[RTraversable
                , Inferrable
                , Recursively (InferOfConstraint KNodes)
                ])
            (from _Flip sequenceC) x

iAnnotations ::
    forall e a b v.
    RTraversable e =>
    Traversal
    (Tree (ITerm a v) e)
    (Tree (ITerm b v) e)
    a b
iAnnotations f (ITerm pl r x) =
    withDict (recursiveKTraversable (Proxy @e)) $
    ITerm
    <$> f pl
    <*> pure r
    <*> traverseKWith (Proxy @'[RTraversable]) (iAnnotations f) x

deriving instance (Show a, Show (Tree e (ITerm a v)), Show (Tree (InferOf e) v)) => Show (Tree (ITerm a v) e)
