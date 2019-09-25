-- | Combinators for processing/constructing trees recursively

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Recurse
    ( module Hyper.Class.Recursive
    , fold, unfold
    , wrap, wrapM, unwrap, unwrapM
    , foldMapRecursive
    , KRecWitness(..)
    , (#>>), (#**#), (##>>)
    ) where

import Hyper.Class.Foldable
import Hyper.Class.Functor (KFunctor(..))
import Hyper.Class.Nodes (KNodes(..), (#>), (#*#))
import Hyper.Class.Recursive
import Hyper.Class.Traversable
import Hyper.Type
import Hyper.Type.Pure (Pure(..), _Pure, (&#))
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | @KRecWitness k n@ is a witness that @n@ is a recursive node of @k@
data KRecWitness k n where
    KRecSelf :: KRecWitness k k
    KRecSub :: KWitness k c -> KRecWitness c n -> KRecWitness k n

-- | Monadically convert a 'Pure' 'Tree' to a different 'Hyper.Type.Knot' from the bottom up
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

-- | Monadically unwrap a 'Tree' from the top down, replacing its 'Hyper.Type.Knot' with 'Pure'
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

-- | Wrap a 'Pure' 'Tree' to a different 'Hyper.Type.Knot' from the bottom up
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

-- | Unwrap a 'Tree' from the top down, replacing its 'Hyper.Type.Knot' with 'Pure'
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
infixr 0 ##>>
infixr 0 #**#

-- | @Proxy @c #> r@ replaces a recursive witness parameter of @r@ with a constraint on the witnessed node
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

-- | @Proxy @c #> r@ replaces a recursive witness parameter of @r@ with a @Recursively c@ constraint on the witnessed node
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

-- | A variant of '#>>' which does not consume the witness parameter.
--
-- @Proxy @c0 #**# Proxy @c1 #>> r@ brings into context both the @c0 n@ and @c1 n@ constraints.
{-# INLINE (#**#) #-}
(#**#) ::
    (Recursive c, c k, RNodes k) =>
    Proxy c -> (KRecWitness k n -> (c n => r)) -> KRecWitness k n -> r
(#**#) p r w = (p #>> r) w w
