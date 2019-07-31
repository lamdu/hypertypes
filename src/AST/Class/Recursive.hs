{-# LANGUAGE NoImplicitPrelude, RankNTypes, DefaultSignatures, TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, DataKinds, TypeFamilies, TypeOperators #-}

module AST.Class.Recursive
    ( Recursively(..), RecursiveContext, RecursiveDict, RecursiveConstraint
    , RecursiveNodes(..), recSelf, recSub
    , RLiftConstraints(..)
    , traverseKRec, foldMapKRec, mapKRec
    , wrap, wrapWithDict
    , wrapM, wrapMWithDict
    , unwrap, unwrapWithDict
    , unwrapM, unwrapMWithDict
    , fold, unfold
    , foldMapRecursive, foldMapRecursiveWithDict
    ) where

import AST.Class
import AST.Class.Combinators
import AST.Class.Foldable
import AST.Class.Traversable
import AST.Combinator.Both
import AST.Combinator.Flip
import AST.Constraint
import AST.Knot (Tree, Node, RunKnot)
import AST.Knot.Dict
import AST.Knot.Pure (Pure(..), _Pure)
import Control.Lens (makeLenses)
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

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
    , KLiftConstraint expr (Recursively constraint)
    )

type RecursiveDict expr constraint = Dict (RecursiveContext expr constraint)

class    Recursively c k => RecursiveConstraint k c
instance Recursively c k => RecursiveConstraint k c

type instance ApplyKnotConstraint (RecursiveConstraint k) c = Recursively c k

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
        withDict (recursive :: RecursiveDict a KNodes) $
        withDict (kNodes (Proxy :: Proxy a)) $
        RecursiveNodes
        { _recSelf = f
        , _recSub = pureKWith (Proxy :: Proxy '[Recursively KNodes]) (_Flip # pureK f)
        }

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        withDict (recP p) $
        withDict (recursive :: RecursiveDict a KNodes) $
        withDict (kNodes (Proxy :: Proxy a)) $
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
        withDict (recursive :: RecursiveDict a KNodes) $
        withDict (kNodes (Proxy :: Proxy a)) $
        RecursiveNodes
        { _recSelf = runMapK fSelf xSelf
        , _recSub =
            mapC
            ( mapKWith (Proxy :: Proxy '[Recursively KNodes])
                ((_MapK #) . (\(MkFlip sf) -> _Flip %~ mapC sf)) fSub
            ) xSub
        }

instance
    Recursively KNodes a =>
    KApply (RecursiveNodes a) where

    {-# INLINE zipK #-}
    zipK (RecursiveNodes xSelf xSub) (RecursiveNodes ySelf ySub) =
        withDict (recursive :: RecursiveDict a KNodes) $
        withDict (kNodes (Proxy :: Proxy a)) $
        RecursiveNodes
        { _recSelf = Both xSelf ySelf
        , _recSub =
            liftK2With (Proxy :: Proxy '[Recursively KNodes])
            (\(MkFlip x) -> _Flip %~ zipK x) xSub ySub
        }

instance constraint Pure => Recursively constraint Pure

type family RecursivelyConstraints cs :: [KnotConstraint] where
    RecursivelyConstraints (c ': cs) = (Recursively c ': RecursivelyConstraints cs)
    RecursivelyConstraints '[] = '[]

class RLiftConstraints k cs where
    rLiftConstraints :: Tree (RecursiveNodes k) (KDict cs)

instance
    Recursively KNodes k =>
    RLiftConstraints k '[] where

    {-# INLINE rLiftConstraints #-}
    rLiftConstraints = pureK (MkKDict Dict)

instance
    (Recursively KNodes k, Recursively c k, RLiftConstraints k cs) =>
    RLiftConstraints k (c ': cs) where

    {-# INLINE rLiftConstraints #-}
    rLiftConstraints =
        liftK2
        (\(MkKDict c) (MkKDict cs) -> withDict c (withDict cs (MkKDict Dict)))
        (pureKWithConstraint (Proxy :: Proxy c) (MkKDict Dict) :: Tree (RecursiveNodes k) (KDict '[c]))
        (rLiftConstraints :: Tree (RecursiveNodes k) (KDict cs))

{-# INLINE mapKRec #-}
mapKRec ::
    forall k cs m n.
    KFunctor k =>
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall c. Tree (RecursiveNodes c) (KDict cs) -> Tree m c -> Tree n c) ->
    Tree k m ->
    Tree k n
mapKRec c f =
    withDict (kNodes (Proxy :: Proxy k)) $
    mapC (mapK (MkMapK . \(MkFlip d) -> f d) (c ^. recSub))

{-# INLINE foldMapKRec #-}
foldMapKRec ::
    forall a k cs n.
    (Monoid a, KFoldable k) =>
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall c. Tree (RecursiveNodes c) (KDict cs) -> Tree n c -> a) ->
    Tree k n ->
    a
foldMapKRec c f =
    withDict (kNodes (Proxy :: Proxy k)) $
    foldMapC (mapK (MkConvertK . \(MkFlip d) -> f d) (c ^. recSub))

{-# INLINE traverseKRec #-}
traverseKRec ::
    forall k cs m n f.
    (Applicative f, KTraversable k) =>
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall c. Tree (RecursiveNodes c) (KDict cs) -> Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseKRec c f =
    withDict (kNodes (Proxy :: Proxy k)) $
    sequenceC .
    mapC (mapK (MkMapK . \(MkFlip d) -> MkContainedK . f d) (c ^. recSub))

{-# INLINE wrapMWithDict #-}
wrapMWithDict ::
    forall k cs w m.
    Monad m =>
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall n. ApplyKConstraints n cs => Dict (KTraversable n)) ->
    (forall n. ApplyKConstraints n cs => Tree n w -> m (Tree w n)) ->
    Tree Pure k ->
    m (Tree w k)
wrapMWithDict c getTraversable f x =
    withDict (c ^. recSelf . _KDict) $
    withDict (getTraversable :: Dict (KTraversable k)) $
    x ^. _Pure
    & traverseKRec c (\d -> wrapMWithDict d getTraversable f)
    >>= f

{-# INLINE wrapM #-}
wrapM ::
    forall m k cs w.
    (Monad m, RLiftConstraints k cs) =>
    Proxy cs ->
    (forall n. ApplyKConstraints n cs => Dict (KTraversable n)) ->
    (forall n. ApplyKConstraints n cs => Tree n w -> m (Tree w n)) ->
    Tree Pure k ->
    m (Tree w k)
wrapM _ =
    wrapMWithDict (rLiftConstraints :: Tree (RecursiveNodes k) (KDict cs))

{-# INLINE unwrapMWithDict #-}
unwrapMWithDict ::
    forall k cs w m.
    Monad m =>
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall n. ApplyKConstraints n cs => Dict (KTraversable n)) ->
    (forall n. ApplyKConstraints n cs => Tree w n -> m (Tree n w)) ->
    Tree w k ->
    m (Tree Pure k)
unwrapMWithDict c getTraversable f x =
    withDict (c ^. recSelf . _KDict) $
    withDict (getTraversable :: Dict (KTraversable k)) $
    f x
    >>= traverseKRec c (\d -> unwrapMWithDict d getTraversable f)
    <&> (_Pure #)

{-# INLINE unwrapM #-}
unwrapM ::
    forall m k cs w.
    (Monad m, RLiftConstraints k cs) =>
    Proxy cs ->
    (forall n. ApplyKConstraints n cs => Dict (KTraversable n)) ->
    (forall n. ApplyKConstraints n cs => Tree w n -> m (Tree n w)) ->
    Tree w k ->
    m (Tree Pure k)
unwrapM _ =
    unwrapMWithDict (rLiftConstraints :: Tree (RecursiveNodes k) (KDict cs))

{-# INLINE wrapWithDict #-}
wrapWithDict ::
    forall k cs w.
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall n. ApplyKConstraints n cs => Dict (KFunctor n)) ->
    (forall n. ApplyKConstraints n cs => Tree n w -> Tree w n) ->
    Tree Pure k ->
    Tree w k
wrapWithDict c getFunctor f x =
    withDict (c ^. recSelf . _KDict) $
    withDict (getFunctor :: Dict (KFunctor k)) $
    x ^. _Pure
    & mapKRec c (\d -> wrapWithDict d getFunctor f)
    & f

{-# INLINE wrap #-}
wrap ::
    forall k cs w.
    RLiftConstraints k cs =>
    Proxy cs ->
    (forall n. ApplyKConstraints n cs => Dict (KFunctor n)) ->
    (forall n. ApplyKConstraints n cs => Tree n w -> Tree w n) ->
    Tree Pure k ->
    Tree w k
wrap _ =
    wrapWithDict (rLiftConstraints :: Tree (RecursiveNodes k) (KDict cs))

{-# INLINE unwrapWithDict #-}
unwrapWithDict ::
    forall k cs w.
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall n. ApplyKConstraints n cs => Dict (KFunctor n)) ->
    (forall n. ApplyKConstraints n cs => Tree w n -> Tree n w) ->
    Tree w k ->
    Tree Pure k
unwrapWithDict c getFunctor f x =
    withDict (c ^. recSelf . _KDict) $
    withDict (getFunctor :: Dict (KFunctor k)) $
    f x
    & mapKRec c (\d -> unwrapWithDict d getFunctor f)
    & MkPure

{-# INLINE unwrap #-}
unwrap ::
    forall k cs w.
    RLiftConstraints k cs =>
    Proxy cs ->
    (forall n. ApplyKConstraints n cs => Dict (KFunctor n)) ->
    (forall n. ApplyKConstraints n cs => Tree w n -> Tree n w) ->
    Tree w k ->
    Tree Pure k
unwrap _ =
    unwrapWithDict (rLiftConstraints :: Tree (RecursiveNodes k) (KDict cs))

-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
{-# INLINE fold #-}
fold ::
    RLiftConstraints k cs =>
    Proxy cs ->
    (forall n. ApplyKConstraints n cs => Dict (KFunctor n)) ->
    (forall n. ApplyKConstraints n cs => Tree n (Const a) -> a) ->
    Tree Pure k ->
    a
fold p getFunctor f = getConst . wrap p getFunctor (Const . f)

-- | Build/load a tree from a seed value.
-- TODO: Is this an "ana-morphism"?
{-# INLINE unfold #-}
unfold ::
    RLiftConstraints k cs =>
    Proxy cs ->
    (forall n. ApplyKConstraints n cs => Dict (KFunctor n)) ->
    (forall n. ApplyKConstraints n cs => a -> Tree n (Const a)) ->
    a ->
    Tree Pure k
unfold p getFunctor f = unwrap p getFunctor (f . getConst) . Const

{-# INLINE foldMapRecursiveWithDict #-}
foldMapRecursiveWithDict ::
    forall cs k a f.
    (Recursively KFoldable f, Monoid a) =>
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall n. ApplyKConstraints n cs => Dict (KFoldable n)) ->
    (forall n g. (ApplyKConstraints n cs, Recursively KFoldable g) => Tree n g -> a) ->
    Tree k f ->
    a
foldMapRecursiveWithDict c getFoldable f x =
    withDict (c ^. recSelf . _KDict) $
    withDict (getFoldable :: Dict (KFoldable k)) $
    withDict (recursive :: RecursiveDict f KFoldable) $
    f x <>
    foldMapKRec c
    ( \d ->
        foldMapKWith (Proxy :: Proxy '[Recursively KFoldable])
        (foldMapRecursiveWithDict d getFoldable f)
    ) x

{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall cs k a f.
    (RLiftConstraints k cs, Recursively KFoldable f, Monoid a) =>
    Proxy cs ->
    (forall n. ApplyKConstraints n cs => Dict (KFoldable n)) ->
    (forall n g. (ApplyKConstraints n cs, Recursively KFoldable g) => Tree n g -> a) ->
    Tree k f ->
    a
foldMapRecursive _ =
    foldMapRecursiveWithDict (rLiftConstraints :: Tree (RecursiveNodes k) (KDict cs))
