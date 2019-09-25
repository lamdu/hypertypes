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

import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))
import Hyper.Class.Foldable
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..), (#>), (#*#))
import Hyper.Class.Recursive
import Hyper.Class.Traversable
import Hyper.Type
import Hyper.Type.Pure (Pure(..), _Pure, (&#))

import Prelude.Compat

-- | @HRecWitness h n@ is a witness that @n@ is a recursive node of @h@
data HRecWitness h n where
    HRecSelf :: HRecWitness h h
    HRecSub :: HWitness h c -> HRecWitness c n -> HRecWitness h n

-- | Monadically convert a 'Pure' 'Tree' to a different 'Hyper.Type.AHyperType' from the bottom up
{-# INLINE wrapM #-}
wrapM ::
    forall m h w.
    (Monad m, RTraversable h) =>
    (forall n. HRecWitness h n -> Tree n w -> m (Tree w n)) ->
    Tree Pure h ->
    m (Tree w h)
wrapM f x =
    withDict (recurse (Proxy @(RTraversable h))) $
    x ^. _Pure
    & traverseH (Proxy @RTraversable #*# \w -> wrapM (f . HRecSub w))
    >>= f HRecSelf

-- | Monadically unwrap a 'Tree' from the top down, replacing its 'Hyper.Type.AHyperType' with 'Pure'
{-# INLINE unwrapM #-}
unwrapM ::
    forall m h w.
    (Monad m, RTraversable h) =>
    (forall n. HRecWitness h n -> Tree w n -> m (Tree n w)) ->
    Tree w h ->
    m (Tree Pure h)
unwrapM f x =
    withDict (recurse (Proxy @(RTraversable h))) $
    f HRecSelf x
    >>= traverseH (Proxy @RTraversable #*# \w -> unwrapM (f . HRecSub w))
    <&> (_Pure #)

-- | Wrap a 'Pure' 'Tree' to a different 'Hyper.Type.AHyperType' from the bottom up
{-# INLINE wrap #-}
wrap ::
    forall h w.
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> Tree n w -> Tree w n) ->
    Tree Pure h ->
    Tree w h
wrap f x =
    withDict (recursively (Proxy @(HFunctor h))) $
    x ^. _Pure
    & mapH (Proxy @(Recursively HFunctor) #*# \w -> wrap (f . HRecSub w))
    & f HRecSelf

-- | Unwrap a 'Tree' from the top down, replacing its 'Hyper.Type.AHyperType' with 'Pure'
{-# INLINE unwrap #-}
unwrap ::
    forall h w.
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> Tree w n -> Tree n w) ->
    Tree w h ->
    Tree Pure h
unwrap f x =
    withDict (recursively (Proxy @(HFunctor h))) $
    f HRecSelf x
    &# mapH (Proxy @(Recursively HFunctor) #*# \w -> unwrap (f . HRecSub w))

-- | Recursively fold up a tree to produce a result (aka catamorphism)
{-# INLINE fold #-}
fold ::
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> Tree n (Const a) -> a) ->
    Tree Pure h ->
    a
fold f = getConst . wrap (fmap Const . f)

-- | Build/load a tree from a seed value (aka anamorphism)
{-# INLINE unfold #-}
unfold ::
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> a -> Tree n (Const a)) ->
    a ->
    Tree Pure h
unfold f = unwrap (fmap (. getConst) f) . Const

-- | Fold over all of the recursive child nodes of a 'Tree' in pre-order
{-# INLINE foldMapRecursive #-}
foldMapRecursive ::
    forall h p a.
    (Recursively HFoldable h, Recursively HFoldable p, Monoid a) =>
    (forall n q. HRecWitness h n -> Tree n q -> a) ->
    Tree h p ->
    a
foldMapRecursive f x =
    withDict (recursively (Proxy @(HFoldable h))) $
    withDict (recursively (Proxy @(HFoldable p))) $
    f HRecSelf x <>
    foldMapH
    ( Proxy @(Recursively HFoldable) #*#
        \w -> foldMapH (Proxy @(Recursively HFoldable) #> foldMapRecursive (f . HRecSub w))
    ) x

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
    withDict (recurse (Proxy @(RNodes h))) $
    withDict (recurse (Proxy @(c h))) $
    (Proxy @RNodes #*# p #> (p #>> r) w1) w0

-- | @Proxy @c #> r@ replaces a recursive witness parameter of @r@ with a @Recursively c@ constraint on the witnessed node
{-# INLINE (##>>) #-}
(##>>) ::
    forall c h n r.
    Recursively c h =>
    Proxy c -> (c n => r) -> HRecWitness h n -> r
(##>>) p r =
    withDict (recursively (Proxy @(c h))) $
    \case
    HRecSelf -> r
    HRecSub w0 w1 -> (Proxy @(Recursively c) #> (p ##>> r) w1) w0

-- | A variant of '#>>' which does not consume the witness parameter.
--
-- @Proxy @c0 #**# Proxy @c1 #>> r@ brings into context both the @c0 n@ and @c1 n@ constraints.
{-# INLINE (#**#) #-}
(#**#) ::
    (Recursive c, c h, RNodes h) =>
    Proxy c -> (HRecWitness h n -> (c n => r)) -> HRecWitness h n -> r
(#**#) p r w = (p #>> r) w w
