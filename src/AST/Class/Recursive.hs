{-# LANGUAGE RankNTypes, DefaultSignatures, GADTs, FlexibleContexts #-}

module AST.Class.Recursive
    ( Recursive(..)
    , fold, unfold
    , wrap, wrapM, unwrap, unwrapM
    , foldMapRecursive
    , RNodes, RFunctor, RFoldable, RTraversable
    , KRecWitness(..)
    ) where

import AST.Class.Foldable
import AST.Class.Functor (KFunctor(..))
import AST.Class.Nodes (KNodes(..), (#>))
import AST.Class.Traversable
import AST.Knot
import AST.Knot.Pure (Pure(..), _Pure, (&#))
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Constraint.List (And)
import Data.Functor.Const (Const(..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A class of constraint constructors that apply to all recursive child nodes
class Recursive c where
    -- | Lift a recursive constraint to the next layer
    recurse :: (KNodes k, c k) => Proxy (c k) -> Dict (KNodesConstraint k c)

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

-- | A class of 'Knot's which recursively implement 'KNodes'
class KNodes k => RNodes k where
    recursiveKNodes :: Proxy k -> Dict (KNodesConstraint k RNodes)
    {-# INLINE recursiveKNodes #-}
    default recursiveKNodes ::
        KNodesConstraint k RNodes =>
        Proxy k -> Dict (KNodesConstraint k RNodes)
    recursiveKNodes _ = Dict

instance RNodes Pure
instance RNodes (Const a)

argP :: Proxy (f k :: Constraint) -> Proxy (k :: Knot -> Type)
argP _ = Proxy

instance Recursive RNodes where
    {-# INLINE recurse #-}
    recurse = recursiveKNodes . argP

-- | A class of 'Knot's which recursively implement 'KFunctor'
class (KFunctor k, RNodes k) => RFunctor k where
    recursiveKFunctor :: Proxy k -> Dict (KNodesConstraint k RFunctor)
    {-# INLINE recursiveKFunctor #-}
    default recursiveKFunctor ::
        KNodesConstraint k RFunctor =>
        Proxy k -> Dict (KNodesConstraint k RFunctor)
    recursiveKFunctor _ = Dict

instance RFunctor Pure
instance RFunctor (Const a)

instance Recursive RFunctor where
    {-# INLINE recurse #-}
    recurse = recursiveKFunctor . argP

-- | A class of 'Knot's which recursively implement 'KFoldable'
class (KFoldable k, RNodes k) => RFoldable k where
    recursiveKFoldable :: Proxy k -> Dict (KNodesConstraint k RFoldable)
    {-# INLINE recursiveKFoldable #-}
    default recursiveKFoldable ::
        KNodesConstraint k RFoldable =>
        Proxy k -> Dict (KNodesConstraint k RFoldable)
    recursiveKFoldable _ = Dict

instance RFoldable Pure
instance RFoldable (Const a)

instance Recursive RFoldable where
    {-# INLINE recurse #-}
    recurse = recursiveKFoldable . argP

-- | A class of 'Knot's which recursively implement 'KTraversable'
class (KTraversable k, RFunctor k, RFoldable k) => RTraversable k where
    recursiveKTraversable :: Proxy k -> Dict (KNodesConstraint k RTraversable)
    {-# INLINE recursiveKTraversable #-}
    default recursiveKTraversable ::
        KNodesConstraint k RTraversable =>
        Proxy k -> Dict (KNodesConstraint k RTraversable)
    recursiveKTraversable _ = Dict

instance RTraversable Pure
instance RTraversable (Const a)

instance Recursive RTraversable where
    {-# INLINE recurse #-}
    recurse = recursiveKTraversable . argP

-- | Monadically convert a 'Pure' 'Tree' to a different 'Knot' from the bottom up
{-# INLINE wrapM #-}
wrapM ::
    forall m k c w.
    (Monad m, Recursive c, RTraversable k, c k) =>
    Proxy c ->
    (forall n. c n => Tree n w -> m (Tree w n)) ->
    Tree Pure k ->
    m (Tree w k)
wrapM p f x =
    withDict (recurse (Proxy @(And RTraversable c k))) $
    x ^. _Pure
    & traverseK (Proxy @(And RTraversable c) #> wrapM p f)
    >>= f

-- | Monadically unwrap a 'Tree' from the top down, replacing its 'Knot' with 'Pure'
{-# INLINE unwrapM #-}
unwrapM ::
    forall m k c w.
    (Monad m, Recursive c, RTraversable k, c k) =>
    Proxy c ->
    (forall n. c n => Tree w n -> m (Tree n w)) ->
    Tree w k ->
    m (Tree Pure k)
unwrapM p f x =
    withDict (recurse (Proxy @(And RTraversable c k))) $
    f x
    >>= traverseK (Proxy @(And RTraversable c) #> unwrapM p f)
    <&> (_Pure #)

-- | Wrap a 'Pure' 'Tree' to a different 'Knot' from the bottom up
{-# INLINE wrap #-}
wrap ::
    forall k c w.
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => Tree n w -> Tree w n) ->
    Tree Pure k ->
    Tree w k
wrap p f x =
    withDict (recurse (Proxy @(And RFunctor c k))) $
    x ^. _Pure
    & mapK (Proxy @(And RFunctor c) #> wrap p f)
    & f

-- | Unwrap a 'Tree' from the top down, replacing its 'Knot' with 'Pure'
{-# INLINE unwrap #-}
unwrap ::
    forall k c w.
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => Tree w n -> Tree n w) ->
    Tree w k ->
    Tree Pure k
unwrap p f x =
    withDict (recurse (Proxy @(And RFunctor c k))) $
    f x
    &# mapK (Proxy @(And RFunctor c) #> unwrap p f)

-- | Recursively fold up a tree to produce a result (aka catamorphism)
{-# INLINE fold #-}
fold ::
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => Tree n (Const a) -> a) ->
    Tree Pure k ->
    a
fold p f = getConst . wrap p (Const . f)

-- | Build/load a tree from a seed value (aka anamorphism)
{-# INLINE unfold #-}
unfold ::
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => a -> Tree n (Const a)) ->
    a ->
    Tree Pure k
unfold p f = unwrap p (f . getConst) . Const

-- | Fold over all of the recursive child nodes of a 'Tree' in pre-order
{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall c k a f.
    (Recursive c, RFoldable k, c k, RFoldable f, Monoid a) =>
    Proxy c ->
    (forall n g. c n => Tree n g -> a) ->
    Tree k f ->
    a
foldMapRecursive p f x =
    withDict (recurse (Proxy @(And RFoldable c k))) $
    withDict (recurse (Proxy @(RFoldable f))) $
    f x <>
    foldMapK
    ( Proxy @(And RFoldable c) #>
        foldMapK (Proxy @RFoldable #> foldMapRecursive p f)
    ) x

-- TODO: Should KRecWitness be here?

-- | @KRecWitness k n@ is a witness that @n@ is a recursive node of @k@
data KRecWitness k n where
    KRecSelf :: KRecWitness k k
    KRecSub :: KWitness k c -> KRecWitness c n -> KRecWitness k n
