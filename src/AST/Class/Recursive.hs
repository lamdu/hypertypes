{-# LANGUAGE RankNTypes, DefaultSignatures, GADTs, FlexibleContexts, FlexibleInstances #-}

module AST.Class.Recursive
    ( Recursive(..)
    , fold, unfold
    , wrap, wrapM, unwrap, unwrapM
    , foldMapRecursive
    , Recursively(..)
    , RNodes, RTraversable
    , KRecWitness(..)
    , (#>>), (#**#), (##>>)
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

-- | A constraint lifted to apply recursively.
--
-- Note that in cases where a constraint has dependencies other than 'RNodes',
-- one will want to create a class such as RTraversable to capture the dependencies,
-- otherwise using it in class contexts will be quite unergonomic.
class RNodes k => Recursively c k where
    recursively ::
        Proxy (c k) -> Dict (c k, KNodesConstraint k (Recursively c))
    {-# INLINE recursively #-}
    default recursively ::
        (c k, KNodesConstraint k (Recursively c)) =>
        Proxy (c k) -> Dict (c k, KNodesConstraint k (Recursively c))
    recursively _ = Dict

instance Recursive (Recursively c) where
    {-# INLINE recurse #-}
    recurse p =
        withDict (recursively (p0 p)) Dict
        where
            p0 :: Proxy (Recursively c k) -> Proxy (c k)
            p0 _ = Proxy

instance c Pure => Recursively c Pure
instance c (Const a) => Recursively c (Const a)

-- | A class of 'Knot's which recursively implement 'KTraversable'
class (KTraversable k, Recursively KFunctor k, Recursively KFoldable k) => RTraversable k where
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
    Recursively KFunctor k =>
    (forall n. KRecWitness k n -> Tree n w -> Tree w n) ->
    Tree Pure k ->
    Tree w k
wrap f x =
    withDict (recursively (Proxy @(KFunctor k))) $
    x ^. _Pure
    & mapK (Proxy @(Recursively KFunctor) #*# \w -> wrap (f . KRecSub w))
    & f KRecSelf

-- | Unwrap a 'Tree' from the top down, replacing its 'Knot' with 'Pure'
{-# INLINE unwrap #-}
unwrap ::
    forall k w.
    Recursively KFunctor k =>
    (forall n. KRecWitness k n -> Tree w n -> Tree n w) ->
    Tree w k ->
    Tree Pure k
unwrap f x =
    withDict (recursively (Proxy @(KFunctor k))) $
    f KRecSelf x
    &# mapK (Proxy @(Recursively KFunctor) #*# \w -> unwrap (f . KRecSub w))

-- | Recursively fold up a tree to produce a result (aka catamorphism)
{-# INLINE fold #-}
fold ::
    Recursively KFunctor k =>
    (forall n. KRecWitness k n -> Tree n (Const a) -> a) ->
    Tree Pure k ->
    a
fold f = getConst . wrap (fmap Const . f)

-- | Build/load a tree from a seed value (aka anamorphism)
{-# INLINE unfold #-}
unfold ::
    Recursively KFunctor k =>
    (forall n. KRecWitness k n -> a -> Tree n (Const a)) ->
    a ->
    Tree Pure k
unfold f = unwrap (fmap (. getConst) f) . Const

-- | Fold over all of the recursive child nodes of a 'Tree' in pre-order
{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall k p a.
    (Recursively KFoldable k, Recursively KFoldable p, Monoid a) =>
    (forall n q. KRecWitness k n -> Tree n q -> a) ->
    Tree k p ->
    a
foldMapRecursive f x =
    withDict (recursively (Proxy @(KFoldable k))) $
    withDict (recursively (Proxy @(KFoldable p))) $
    f KRecSelf x <>
    foldMapK
    ( Proxy @(Recursively KFoldable) #*#
        \w -> foldMapK (Proxy @(Recursively KFoldable) #> foldMapRecursive (f . KRecSub w))
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

{-# INLINE (##>>) #-}
(##>>) ::
    forall c k n r.
    Recursively c k =>
    Proxy c -> (c n => r) -> KRecWitness k n -> r
(##>>) p r =
    withDict (recursively (Proxy @(c k))) $
    \case
    KRecSelf -> r
    KRecSub w0 w1 -> (Proxy @(Recursively c) #> (p ##>> r) w1) w0
