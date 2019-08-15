{-# LANGUAGE RankNTypes, DefaultSignatures, TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables, UndecidableInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableSuperClasses, FlexibleInstances #-}

module AST.Class.Recursive
    ( Recursive(..)
    , RFunctor(..), RFoldable(..), RTraversable(..)
    , Recursively(..), RecursiveContext, RecursiveDict, RecursiveConstraint
    , RecursiveNodes(..), recSelf, recSub
    , wrap, wrapM, unwrap, unwrapM
    , fold, unfold
    ) where

import AST.Class
import AST.Class.Combinators
import AST.Class.Foldable
import AST.Class.Traversable
import AST.Combinator.Flip
import AST.Knot
import AST.Knot.Pure (Pure(..), _Pure)
import Control.Lens (makeLenses)
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Kind (Type, Constraint)
import Data.Proxy (Proxy(..))
import Data.TyFun

import Prelude.Compat

class Recursive c where
    recurse :: c k => Proxy (c k) -> Dict (NodesConstraint k $ c)

class (KFunctor k, Recursively KNodes k) => RFunctor k where
    recursiveKFunctor :: Proxy k -> Dict (NodesConstraint k $ RFunctor)
    {-# INLINE recursiveKFunctor #-}
    default recursiveKFunctor ::
        NodesConstraint k $ RFunctor =>
        Proxy k -> Dict (NodesConstraint k $ RFunctor)
    recursiveKFunctor _ = Dict

instance Recursive RFunctor where
    {-# INLINE recurse #-}
    recurse =
        recursiveKFunctor . p
        where
            p :: Proxy (RFunctor k) -> Proxy k
            p _ = Proxy

class (KFoldable k, Recursively KNodes k) => RFoldable k where
    recursiveKFoldable :: Proxy k -> Dict (NodesConstraint k $ RFoldable)
    {-# INLINE recursiveKFoldable #-}
    default recursiveKFoldable ::
        NodesConstraint k $ RFoldable =>
        Proxy k -> Dict (NodesConstraint k $ RFoldable)
    recursiveKFoldable _ = Dict

instance Recursive RFoldable where
    {-# INLINE recurse #-}
    recurse =
        recursiveKFoldable . p
        where
            p :: Proxy (RFoldable k) -> Proxy k
            p _ = Proxy

class (KTraversable k, RFunctor k, RFoldable k) => RTraversable k where
    recursiveKTraversable :: Proxy k -> Dict (NodesConstraint k $ RTraversable)
    {-# INLINE recursiveKTraversable #-}
    default recursiveKTraversable ::
        NodesConstraint k $ RTraversable =>
        Proxy k -> Dict (NodesConstraint k $ RTraversable)
    recursiveKTraversable _ = Dict

instance Recursive RTraversable where
    {-# INLINE recurse #-}
    recurse =
        recursiveKTraversable . p
        where
            p :: Proxy (RTraversable k) -> Proxy k
            p _ = Proxy

-- | `Recursively` carries a constraint to all of the descendant types
-- of an AST. As opposed to the `ChildrenConstraint` type family which
-- only carries a constraint to the direct children of an AST.
class constraint expr => Recursively constraint expr where
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
    , NodesConstraint expr $ Recursively constraint
    )

type RecursiveDict expr constraint = Dict (RecursiveContext expr constraint)

data RecursiveConstraint :: (Knot -> Type) -> ((Knot -> Type) -> Constraint) ~> Constraint

type instance Apply (RecursiveConstraint k) c = Recursively c k

instance Recursive (Recursively c) where
    {-# INLINE recurse #-}
    recurse p =
        withDict (r p) Dict
        where
            r :: Recursively c t => Proxy (Recursively c t) -> RecursiveDict t c
            r _ = recursive

data RecursiveNodes a k = RecursiveNodes
    { _recSelf :: Node k a
    , _recSub :: Tree (NodeTypesOf a) (Flip RecursiveNodes (RunKnot k))
    }
makeLenses ''RecursiveNodes

instance
    Recursively KNodes a =>
    KNodes (RecursiveNodes a) where
    type NodeTypesOf (RecursiveNodes a) = RecursiveNodes a
    type NodesConstraint (RecursiveNodes a) = RecursiveConstraint a

instance
    Recursively KNodes a =>
    KPointed (RecursiveNodes a) where

    {-# INLINE pureK #-}
    pureK f =
        withDict (recursive @KNodes @a) $
        withDict (kNodes (Proxy @a)) $
        RecursiveNodes
        { _recSelf = f
        , _recSub = pureKWithConstraint (Proxy @(Recursively KNodes)) (_Flip # pureK f)
        }

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        withDict (recP p) $
        withDict (recursive @KNodes @a) $
        withDict (kNodes (Proxy @a)) $
        RecursiveNodes
        { _recSelf = f
        , _recSub = pureKWith (mkP p) (_Flip # pureKWithConstraint p f)
        }
        where
            recP :: Recursively c a => Proxy c -> RecursiveDict a c
            recP _ = recursive
            mkP :: Proxy c -> Proxy '[Recursively KNodes, Recursively c]
            mkP _ = Proxy

instance
    Recursively KNodes a =>
    KFunctor (RecursiveNodes a) where

    {-# INLINE mapC #-}
    mapC (RecursiveNodes fSelf fSub) (RecursiveNodes xSelf xSub) =
        withDict (recursive @KNodes @a) $
        withDict (kNodes (Proxy @a)) $
        RecursiveNodes
        { _recSelf = runMapK fSelf xSelf
        , _recSub =
            mapC
            ( mapKWith (Proxy @'[Recursively KNodes])
                ((_MapK #) . (\(MkFlip sf) -> _Flip %~ mapC sf)) fSub
            ) xSub
        }

instance
    Recursively KNodes a =>
    KApply (RecursiveNodes a) where

    {-# INLINE zipK #-}
    zipK (RecursiveNodes xSelf xSub) (RecursiveNodes ySelf ySub) =
        withDict (recursive @KNodes @a) $
        withDict (kNodes (Proxy @a)) $
        RecursiveNodes
        { _recSelf = Pair xSelf ySelf
        , _recSub =
            liftK2With (Proxy @'[Recursively KNodes])
            (\(MkFlip x) -> _Flip %~ zipK x) xSub ySub
        }

instance constraint Pure => Recursively constraint Pure

{-# INLINE wrapM #-}
wrapM ::
    forall m k c w.
    (Monad m, Recursive c, c k) =>
    Proxy c ->
    (forall n. c n => Dict (KTraversable n)) ->
    (forall n. c n => Tree n w -> m (Tree w n)) ->
    Tree Pure k ->
    m (Tree w k)
wrapM p getTraversable f x =
    withDict (recurse (Proxy @(c k))) $
    withDict (getTraversable @k) $
    x ^. _Pure
    & traverseKWith (Proxy @'[c]) (wrapM p getTraversable f)
    >>= f

{-# INLINE unwrapM #-}
unwrapM ::
    forall m k c w.
    (Monad m, Recursive c, c k) =>
    Proxy c ->
    (forall n. c n => Dict (KTraversable n)) ->
    (forall n. c n => Tree w n -> m (Tree n w)) ->
    Tree w k ->
    m (Tree Pure k)
unwrapM p getTraversable f x =
    withDict (recurse (Proxy @(c k))) $
    withDict (getTraversable @k) $
    f x
    >>= traverseKWith (Proxy @'[c]) (unwrapM p getTraversable f)
    <&> (_Pure #)

{-# INLINE wrap #-}
wrap ::
    forall k c w.
    (Recursive c, c k) =>
    Proxy c ->
    (forall n. c n => Dict (KFunctor n)) ->
    (forall n. c n => Tree n w -> Tree w n) ->
    Tree Pure k ->
    Tree w k
wrap p getFunctor f x =
    withDict (recurse (Proxy @(c k))) $
    withDict (getFunctor @k) $
    x ^. _Pure
    & mapKWith (Proxy @'[c]) (wrap p getFunctor f)
    & f

{-# INLINE unwrap #-}
unwrap ::
    forall k c w.
    (Recursive c, c k) =>
    Proxy c ->
    (forall n. c n => Dict (KFunctor n)) ->
    (forall n. c n => Tree w n -> Tree n w) ->
    Tree w k ->
    Tree Pure k
unwrap p getFunctor f x =
    withDict (recurse (Proxy @(c k))) $
    withDict (getFunctor @k) $
    f x
    & mapKWith (Proxy @'[c]) (unwrap p getFunctor f)
    & MkPure

-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
{-# INLINE fold #-}
fold ::
    (Recursive c, c k) =>
    Proxy c ->
    (forall n. c n => Dict (KFunctor n)) ->
    (forall n. c n => Tree n (Const a) -> a) ->
    Tree Pure k ->
    a
fold p getFunctor f = getConst . wrap p getFunctor (Const . f)

-- | Build/load a tree from a seed value.
-- TODO: Is this an "ana-morphism"?
{-# INLINE unfold #-}
unfold ::
    (Recursive c, c k) =>
    Proxy c ->
    (forall n. c n => Dict (KFunctor n)) ->
    (forall n. c n => a -> Tree n (Const a)) ->
    a ->
    Tree Pure k
unfold p getFunctor f = unwrap p getFunctor (f . getConst) . Const
