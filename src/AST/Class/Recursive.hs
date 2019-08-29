{-# LANGUAGE RankNTypes, DefaultSignatures #-}

module AST.Class.Recursive
    ( Recursive(..)
    , RNodes(..), RFunctor(..), RFoldable(..), RTraversable(..)
    , RZipMatch(..), RZipMatchTraversable(..)
    , recurseBoth
    , wrap, wrapM, unwrap, unwrapM
    , fold, unfold
    , foldMapRecursive
    ) where

import AST.Class.Foldable
import AST.Class.Functor (KFunctor(..))
import AST.Class.Nodes (KNodes(..))
import AST.Class.Traversable
import AST.Class.ZipMatch
import AST.Knot
import AST.Knot.Pure (Pure(..), _Pure, (&#))
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Constraint.List (NoConstraint, And)
import Data.Functor.Const (Const(..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class Recursive c where
    recurse :: (KNodes k, c k) => Proxy (c k) -> Dict (NodesConstraint k c)

instance Recursive NoConstraint where
    recurse p = withDict (kNoConstraints (argP p)) Dict

instance (Recursive a, Recursive b) => Recursive (And a b) where
    recurse p =
        withDict (recurse (p0 p)) $
        withDict (recurse (p1 p)) $
        withDict (kCombineConstraints p) Dict
        where
            p0 :: Proxy (And a b k) -> Proxy (a k)
            p0 _ = Proxy
            p1 :: Proxy (And a b k) -> Proxy (b k)
            p1 _ = Proxy

class KNodes k => RNodes k where
    recursiveKNodes :: Proxy k -> Dict (NodesConstraint k RNodes)
    {-# INLINE recursiveKNodes #-}
    default recursiveKNodes ::
        NodesConstraint k RNodes =>
        Proxy k -> Dict (NodesConstraint k RNodes)
    recursiveKNodes _ = Dict

instance RNodes Pure
instance RNodes (Const a)

argP :: Proxy (f k :: Constraint) -> Proxy (k :: Knot -> Type)
argP _ = Proxy

instance Recursive RNodes where
    {-# INLINE recurse #-}
    recurse = recursiveKNodes . argP

class (KFunctor k, RNodes k) => RFunctor k where
    recursiveKFunctor :: Proxy k -> Dict (NodesConstraint k RFunctor)
    {-# INLINE recursiveKFunctor #-}
    default recursiveKFunctor ::
        NodesConstraint k RFunctor =>
        Proxy k -> Dict (NodesConstraint k RFunctor)
    recursiveKFunctor _ = Dict

instance RFunctor Pure
instance RFunctor (Const a)

instance Recursive RFunctor where
    {-# INLINE recurse #-}
    recurse = recursiveKFunctor . argP

class (KFoldable k, RNodes k) => RFoldable k where
    recursiveKFoldable :: Proxy k -> Dict (NodesConstraint k RFoldable)
    {-# INLINE recursiveKFoldable #-}
    default recursiveKFoldable ::
        NodesConstraint k RFoldable =>
        Proxy k -> Dict (NodesConstraint k RFoldable)
    recursiveKFoldable _ = Dict

instance RFoldable Pure
instance RFoldable (Const a)

instance Recursive RFoldable where
    {-# INLINE recurse #-}
    recurse = recursiveKFoldable . argP

class (KTraversable k, RFunctor k, RFoldable k) => RTraversable k where
    recursiveKTraversable :: Proxy k -> Dict (NodesConstraint k RTraversable)
    {-# INLINE recursiveKTraversable #-}
    default recursiveKTraversable ::
        NodesConstraint k RTraversable =>
        Proxy k -> Dict (NodesConstraint k RTraversable)
    recursiveKTraversable _ = Dict

instance RTraversable Pure
instance RTraversable (Const a)

instance Recursive RTraversable where
    {-# INLINE recurse #-}
    recurse = recursiveKTraversable . argP

class (ZipMatch k, RNodes k) => RZipMatch k where
    recursiveZipMatch :: Proxy k -> Dict (NodesConstraint k RZipMatch)
    {-# INLINE recursiveZipMatch #-}
    default recursiveZipMatch ::
        NodesConstraint k RZipMatch =>
        Proxy k -> Dict (NodesConstraint k RZipMatch)
    recursiveZipMatch _ = Dict

instance RZipMatch Pure
instance Eq a => RZipMatch (Const a)

instance Recursive RZipMatch where
    {-# INLINE recurse #-}
    recurse = recursiveZipMatch . argP

class (RTraversable k, RZipMatch k) => RZipMatchTraversable k where
    recursiveZipMatchTraversable :: Proxy k -> Dict (NodesConstraint k RZipMatchTraversable)
    {-# INLINE recursiveZipMatchTraversable #-}
    default recursiveZipMatchTraversable ::
        NodesConstraint k RZipMatchTraversable =>
        Proxy k -> Dict (NodesConstraint k RZipMatchTraversable)
    recursiveZipMatchTraversable _ = Dict

instance RZipMatchTraversable Pure
instance Eq a => RZipMatchTraversable (Const a)

instance Recursive RZipMatchTraversable where
    {-# INLINE recurse #-}
    recurse = recursiveZipMatchTraversable . argP

{-# INLINE recurseBoth #-}
recurseBoth ::
    forall a b k.
    (KNodes k, Recursive a, Recursive b, a k, b k) =>
    Proxy (And a b k) -> Dict (NodesConstraint k (And a b))
recurseBoth _ =
    withDict (recurse (Proxy @(a k))) $
    withDict (recurse (Proxy @(b k))) $
    withDict (kCombineConstraints (Proxy @(And a b k))) Dict

{-# INLINE wrapM #-}
wrapM ::
    forall m k c w.
    (Monad m, Recursive c, RTraversable k, c k) =>
    Proxy c ->
    (forall n. c n => Tree n w -> m (Tree w n)) ->
    Tree Pure k ->
    m (Tree w k)
wrapM p f x =
    withDict (recurseBoth (Proxy @(And RTraversable c k))) $
    x ^. _Pure
    & traverseKWith (Proxy @(And RTraversable c)) (wrapM p f)
    >>= f

{-# INLINE unwrapM #-}
unwrapM ::
    forall m k c w.
    (Monad m, Recursive c, RTraversable k, c k) =>
    Proxy c ->
    (forall n. c n => Tree w n -> m (Tree n w)) ->
    Tree w k ->
    m (Tree Pure k)
unwrapM p f x =
    withDict (recurseBoth (Proxy @(And RTraversable c k))) $
    f x
    >>= traverseKWith (Proxy @(And RTraversable c)) (unwrapM p f)
    <&> (_Pure #)

{-# INLINE wrap #-}
wrap ::
    forall k c w.
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => Tree n w -> Tree w n) ->
    Tree Pure k ->
    Tree w k
wrap p f x =
    withDict (recurseBoth (Proxy @(And RFunctor c k))) $
    x ^. _Pure
    & mapKWith (Proxy @(And RFunctor c)) (wrap p f)
    & f

{-# INLINE unwrap #-}
unwrap ::
    forall k c w.
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => Tree w n -> Tree n w) ->
    Tree w k ->
    Tree Pure k
unwrap p f x =
    withDict (recurseBoth (Proxy @(And RFunctor c k))) $
    f x
    &# mapKWith (Proxy @(And RFunctor c)) (unwrap p f)

-- | Recursively fold up a tree to produce a result.
-- TODO: Is this a "cata-morphism"?
{-# INLINE fold #-}
fold ::
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => Tree n (Const a) -> a) ->
    Tree Pure k ->
    a
fold p f = getConst . wrap p (Const . f)

-- | Build/load a tree from a seed value.
-- TODO: Is this an "ana-morphism"?
{-# INLINE unfold #-}
unfold ::
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => a -> Tree n (Const a)) ->
    a ->
    Tree Pure k
unfold p f = unwrap p (f . getConst) . Const

{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall c k a f.
    (Recursive c, RFoldable k, c k, RFoldable f, Monoid a) =>
    Proxy c ->
    (forall n g. c n => Tree n g -> a) ->
    Tree k f ->
    a
foldMapRecursive p f x =
    withDict (recurseBoth (Proxy @(And RFoldable c k))) $
    withDict (recurse (Proxy @(RFoldable f))) $
    f x <>
    foldMapKWith (Proxy @(And RFoldable c))
    (foldMapKWith (Proxy @RFoldable) (foldMapRecursive p f)) x
