{-# LANGUAGE RankNTypes, DefaultSignatures, GADTs, FlexibleContexts #-}

module AST.Class.Recursive
    ( Recursive(..)
    , fold, unfold
    , wrap, wrapM, unwrap, unwrapM
    , foldMapRecursive
    , RNodes, RFunctor, RFoldable, RTraversable
    , KRecWitness(..), (#>>), (#**#)
    ) where

import AST.Class.Foldable
import AST.Class.Functor (KFunctor(..))
import AST.Class.Nodes (KNodes(..), (#>), (#*#))
import AST.Class.Traversable
import AST.Knot
import AST.Knot.Pure (Pure(..), _Pure, (&#))
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A class of constraint constructors that apply to all recursive child nodes
class Recursive c where
    -- | Lift a recursive constraint to the next layer
    recurse :: (KNodes k, c k) => Proxy (c k) -> Dict (KNodesConstraint k c)

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

-- | @KRecWitness k n@ is a witness that @n@ is a recursive node of @k@
data KRecWitness k n where
    KRecSelf :: KRecWitness k k
    KRecSub :: KWitness k c -> KRecWitness c n -> KRecWitness k n

-- | Monadically convert a 'Pure' 'Tree' to a different 'Knot' from the bottom up
{-# INLINE wrapM #-}
wrapM ::
    forall m k w.
    (Monad m, RTraversable k) =>
    (forall n. KRecWitness k n -> Tree n w -> m (Tree w n)) ->
    Tree Pure k ->
    m (Tree w k)
wrapM f x =
    withDict (recurse (Proxy @(RTraversable k))) $
    x ^. _Pure
    & traverseK (Proxy @RTraversable #*# \w -> wrapM (f . KRecSub w))
    >>= f KRecSelf

-- | Monadically unwrap a 'Tree' from the top down, replacing its 'Knot' with 'Pure'
{-# INLINE unwrapM #-}
unwrapM ::
    forall m k w.
    (Monad m, RTraversable k) =>
    (forall n. KRecWitness k n -> Tree w n -> m (Tree n w)) ->
    Tree w k ->
    m (Tree Pure k)
unwrapM f x =
    withDict (recurse (Proxy @(RTraversable k))) $
    f KRecSelf x
    >>= traverseK (Proxy @RTraversable #*# \w -> unwrapM (f . KRecSub w))
    <&> (_Pure #)

-- | Wrap a 'Pure' 'Tree' to a different 'Knot' from the bottom up
{-# INLINE wrap #-}
wrap ::
    forall k w.
    RFunctor k =>
    (forall n. KRecWitness k n -> Tree n w -> Tree w n) ->
    Tree Pure k ->
    Tree w k
wrap f x =
    withDict (recurse (Proxy @(RFunctor k))) $
    x ^. _Pure
    & mapK (Proxy @RFunctor #*# \w -> wrap (f . KRecSub w))
    & f KRecSelf

-- | Unwrap a 'Tree' from the top down, replacing its 'Knot' with 'Pure'
{-# INLINE unwrap #-}
unwrap ::
    forall k w.
    RFunctor k =>
    (forall n. KRecWitness k n -> Tree w n -> Tree n w) ->
    Tree w k ->
    Tree Pure k
unwrap f x =
    withDict (recurse (Proxy @(RFunctor k))) $
    f KRecSelf x
    &# mapK (Proxy @RFunctor #*# \w -> unwrap (f . KRecSub w))

-- | Recursively fold up a tree to produce a result (aka catamorphism)
{-# INLINE fold #-}
fold ::
    RFunctor k =>
    (forall n. KRecWitness k n -> Tree n (Const a) -> a) ->
    Tree Pure k ->
    a
fold f = getConst . wrap (fmap Const . f)

-- | Build/load a tree from a seed value (aka anamorphism)
{-# INLINE unfold #-}
unfold ::
    RFunctor k =>
    (forall n. KRecWitness k n -> a -> Tree n (Const a)) ->
    a ->
    Tree Pure k
unfold f = unwrap (fmap (. getConst) f) . Const

-- | Fold over all of the recursive child nodes of a 'Tree' in pre-order
{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall k p a.
    (RFoldable k, RFoldable p, Monoid a) =>
    (forall n q. KRecWitness k n -> Tree n q -> a) ->
    Tree k p ->
    a
foldMapRecursive f x =
    withDict (recurse (Proxy @(RFoldable k))) $
    withDict (recurse (Proxy @(RFoldable p))) $
    f KRecSelf x <>
    foldMapK
    ( Proxy @RFoldable #*#
        \w -> foldMapK (Proxy @RFoldable #> foldMapRecursive (f . KRecSub w))
    ) x

infixr 0 #>>
infixr 0 #**#

{-# INLINE (#>>) #-}
(#>>) ::
    forall c k n r.
    (Recursive c, c k, RNodes k) =>
    Proxy c -> (c n => r) -> KRecWitness k n -> r
(#>>) _ r KRecSelf = r
(#>>) p r (KRecSub w0 w1) =
    withDict (recurse (Proxy @(RNodes k))) $
    withDict (recurse (Proxy @(c k))) $
    (Proxy @RNodes #*# p #> (p #>> r) w1) w0

{-# INLINE (#**#) #-}
(#**#) ::
    (Recursive c, c k, RNodes k) =>
    Proxy c -> (KRecWitness k n -> (c n => r)) -> KRecWitness k n -> r
(#**#) p r w = (p #>> r) w w
