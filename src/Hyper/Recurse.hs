-- | Combinators for processing/constructing trees recursively

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Recurse
    ( module Hyper.Class.Recursive
    , fold, unfold
    , wrap, wrapM, unwrap, unwrapM
    , foldMapRecursive
    , HRecWitness(..)
    , (#>>), (#**#), (##>>)
    ) where

import Hyper.Class.Foldable
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HWitness, (#>), (#*#))
import Hyper.Class.Recursive
import Hyper.Class.Traversable
import Hyper.Type
import Hyper.Type.Pure (Pure(..), _Pure)

import Hyper.Internal.Prelude

-- | @HRecWitness h n@ is a witness that @n@ is a recursive node of @h@
data HRecWitness h n where
    HRecSelf :: HRecWitness h h
    HRecSub :: HWitness h c -> HRecWitness c n -> HRecWitness h n

-- | Monadically convert a 'Pure' to a different 'HyperType' from the bottom up
{-# INLINE wrapM #-}
wrapM ::
    forall m h w.
    (Monad m, RTraversable h) =>
    (forall n. HRecWitness h n -> n # w -> m (w # n)) ->
    Pure # h ->
    m (w # h)
wrapM f x =
    x ^. _Pure
    & htraverse (Proxy @RTraversable #*# \w -> wrapM (f . HRecSub w))
    >>= f HRecSelf
    \\ recurse (Proxy @(RTraversable h))

-- | Monadically unwrap a tree from the top down, replacing its 'HyperType' with 'Pure'
{-# INLINE unwrapM #-}
unwrapM ::
    forall m h w.
    (Monad m, RTraversable h) =>
    (forall n. HRecWitness h n -> w # n -> m (n # w)) ->
    w # h ->
    m (Pure # h)
unwrapM f x =
    f HRecSelf x
    >>= htraverse (Proxy @RTraversable #*# \w -> unwrapM (f . HRecSub w))
    <&> (_Pure #)
    \\ recurse (Proxy @(RTraversable h))

-- | Wrap a 'Pure' to a different 'HyperType' from the bottom up
{-# INLINE wrap #-}
wrap ::
    forall h w.
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> n # w -> w # n) ->
    Pure # h ->
    w # h
wrap f x =
    x ^. _Pure
    & hmap (Proxy @(Recursively HFunctor) #*# \w -> wrap (f . HRecSub w))
    & f HRecSelf
    \\ recursively (Proxy @(HFunctor h))

-- | Unwrap a tree from the top down, replacing its 'HyperType' with 'Pure'
{-# INLINE unwrap #-}
unwrap ::
    forall h w.
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> w # n -> n # w) ->
    w # h ->
    Pure # h
unwrap f x =
    _Pure #
    hmap (Proxy @(Recursively HFunctor) #*# \w -> unwrap (f . HRecSub w))
    (f HRecSelf x)
    \\ recursively (Proxy @(HFunctor h))

-- | Recursively fold up a tree to produce a result (aka catamorphism)
{-# INLINE fold #-}
fold ::
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> n # Const a -> a) ->
    Pure # h ->
    a
fold f = getConst . wrap (fmap Const . f)

-- | Build/load a tree from a seed value (aka anamorphism)
{-# INLINE unfold #-}
unfold ::
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> a -> n # Const a) ->
    a ->
    Pure # h
unfold f = unwrap (fmap (. getConst) f) . Const

-- | Fold over all of the recursive child nodes of a tree in pre-order
{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall h p a.
    (Recursively HFoldable h, Recursively HFoldable p, Monoid a) =>
    (forall n q. HRecWitness h n -> n # q -> a) ->
    h # p ->
    a
foldMapRecursive f x =
    f HRecSelf x <>
    hfoldMap
    ( Proxy @(Recursively HFoldable) #*#
        \w ->
            hfoldMap (Proxy @(Recursively HFoldable) #> foldMapRecursive (f . HRecSub w))
            \\ recursively (Proxy @(HFoldable p))
    ) x
    \\ recursively (Proxy @(HFoldable h))

infixr 0 #>>
infixr 0 ##>>
infixr 0 #**#

-- | @Proxy @c #> r@ replaces a recursive witness parameter of @r@ with a constraint on the witnessed node
{-# INLINE (#>>) #-}
(#>>) ::
    forall c h n r.
    (Recursive c, c h, RNodes h) =>
    Proxy c -> (c n => r) -> HRecWitness h n -> r
(#>>) _ r HRecSelf = r
(#>>) p r (HRecSub w0 w1) =
    (Proxy @RNodes #*# p #> (p #>> r) w1) w0
    \\ recurse (Proxy @(RNodes h))
    \\ recurse (Proxy @(c h))

-- | @Proxy @c #> r@ replaces a recursive witness parameter of @r@ with a @Recursively c@ constraint on the witnessed node
{-# INLINE (##>>) #-}
(##>>) ::
    forall c h n r.
    Recursively c h =>
    Proxy c -> (c n => r) -> HRecWitness h n -> r
(##>>) p r =
    \case
    HRecSelf -> r
    HRecSub w0 w1 -> (Proxy @(Recursively c) #> (p ##>> r) w1) w0
    \\ recursively (Proxy @(c h))

-- | A variant of '#>>' which does not consume the witness parameter.
--
-- @Proxy @c0 #**# Proxy @c1 #>> r@ brings into context both the @c0 n@ and @c1 n@ constraints.
{-# INLINE (#**#) #-}
(#**#) ::
    (Recursive c, c h, RNodes h) =>
    Proxy c -> (c n => HRecWitness h n -> r) -> HRecWitness h n -> r
(#**#) p r w = (p #>> r) w w
