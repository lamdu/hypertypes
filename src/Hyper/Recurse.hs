{-# LANGUAGE FlexibleContexts #-}

-- | Combinators for processing/constructing trees recursively
module Hyper.Recurse
    ( module Hyper.Class.Recursive
    , fold
    , unfold
    , wrap
    , wrapM
    , unwrap
    , unwrapM
    , foldMapRecursive
    , HRecWitness (..)
    , recursiveHLiftConstraint
    , (#>>)
    , (#**#)
    , (##>>)
    ) where

import Hyper.Class.Foldable
import Hyper.Class.Functor (HFunctor (..))
import Hyper.Class.Nodes (HWitness (..), HWitnessType, (#*#), (#>))
import Hyper.Class.Recursive
import Hyper.Class.Traversable
import Hyper.Type
import Hyper.Type.Pure (Pure (..), _Pure)

import Hyper.Internal.Prelude

-- | @HRecWitness h n@ is a witness that @n@ is a recursive node of @h@
data HRecWitness h n where
    HRecSelf :: HRecWitness h h
    HRecSub :: HRecWitness h c -> HWitness c n -> HRecWitness h n

-- | Monadically convert a 'Pure' to a different 'HyperType' from the bottom up
{-# INLINE wrapM #-}
wrapM ::
    forall m h w.
    (Monad m, RTraversable h) =>
    (forall n. HRecWitness h n -> n # w -> m (w # n)) ->
    Pure # h ->
    m (w # h)
wrapM f =
    go HRecSelf
    where
        go :: forall c. RTraversable c => HRecWitness h c -> Pure # c -> m (w # c)
        go prefix (Pure x) =
            htraverseRec prefix go x >>= f prefix

-- | Monadically unwrap a tree from the top down, replacing its 'HyperType' with 'Pure'
{-# INLINE unwrapM #-}
unwrapM ::
    forall m h w.
    (Monad m, RTraversable h) =>
    (forall n. HRecWitness h n -> w # n -> m (n # w)) ->
    w # h ->
    m (Pure # h)
unwrapM f =
    go HRecSelf
    where
        go :: forall c. RTraversable c => HRecWitness h c -> w # c -> m (Pure # c)
        go prefix x =
            f prefix x >>= htraverseRec prefix go <&> (_Pure #)

{-# INLINE htraverseRec #-}
htraverseRec ::
    forall f h c p q.
    (Applicative f, RTraversable c) =>
    HRecWitness h c ->
    (forall n. RTraversable n => HRecWitness h n -> p # n -> f (q # n)) ->
    c # p ->
    f (c # q)
htraverseRec prefix f =
    htraverse (Proxy @RTraversable #*# f . HRecSub prefix)
        \\ recurse (Proxy @(RTraversable c))

-- | Wrap a 'Pure' to a different 'HyperType' from the bottom up
{-# INLINE wrap #-}
wrap ::
    forall h w.
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> n # w -> w # n) ->
    Pure # h ->
    w # h
wrap f =
    go HRecSelf
    where
        go :: forall c. Recursively HFunctor c => HRecWitness h c -> Pure # c -> w # c
        go prefix (Pure x) = f prefix (hmapRec prefix go x)

-- | Unwrap a tree from the top down, replacing its 'HyperType' with 'Pure'
{-# INLINE unwrap #-}
unwrap ::
    forall h w.
    Recursively HFunctor h =>
    (forall n. HRecWitness h n -> w # n -> n # w) ->
    w # h ->
    Pure # h
unwrap f =
    go HRecSelf
    where
        go :: forall c. Recursively HFunctor c => HRecWitness h c -> w # c -> Pure # c
        go prefix x = _Pure # hmapRec prefix go (f prefix x)

{-# INLINE hmapRec #-}
hmapRec ::
    forall h c p q.
    Recursively HFunctor c =>
    HRecWitness h c ->
    (forall n. Recursively HFunctor n => HRecWitness h n -> p # n -> q # n) ->
    c # p ->
    c # q
hmapRec prefix f =
    hmap (Proxy @(Recursively HFunctor) #*# f . HRecSub prefix)
        \\ recursively (Proxy @(HFunctor c))

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
foldMapRecursive f =
    go HRecSelf
    where
        go :: forall c q. (Recursively HFoldable c, Recursively HFoldable q) => HRecWitness h c -> c # q -> a
        go prefix x =
            f prefix x
                <> hfoldMap
                    ( Proxy @(Recursively HFoldable) #*#
                        \w ->
                            hfoldMap (Proxy @(Recursively HFoldable) #> go (HRecSub prefix w))
                                \\ recursively (Proxy @(HFoldable q))
                    )
                    x
                \\ recursively (Proxy @(HFoldable c))

infixr 0 #>>
infixr 0 ##>>
infixr 0 #**#

{-# INLINE recursiveHLiftConstraint #-}
recursiveHLiftConstraint ::
    forall h wrapper n c r.
    (Recursive c, c h, RNodes h, HWitnessType wrapper ~ HRecWitness h) =>
    HWitness wrapper n ->
    Proxy c ->
    (c n => r) ->
    r
recursiveHLiftConstraint (HWitness w) p f = (p #>> f) w

-- | @Proxy @c #> r@ replaces a recursive witness parameter of @r@ with a constraint on the witnessed node
{-# INLINE (#>>) #-}
(#>>) ::
    forall c h n r.
    (Recursive c, c h, RNodes h) =>
    Proxy c ->
    (c n => r) ->
    HRecWitness h n ->
    r
(#>>) _ = go
    where
        go :: forall p. (c p => RNodes p => r) -> HRecWitness h p -> r
        go x HRecSelf = x
        go x (HRecSub (prefix :: HRecWitness h q) child) =
            go
                ( (Proxy @c #*# \child' -> (Proxy @RNodes #> x) child') child
                    \\ recurse (Proxy @(c q))
                    \\ recurse (Proxy @(RNodes q))
                )
                prefix

-- | @Proxy @c #> r@ replaces a recursive witness parameter of @r@ with a @Recursively c@ constraint on the witnessed node
{-# INLINE (##>>) #-}
(##>>) ::
    forall c h n r.
    Recursively c h =>
    Proxy c ->
    (c n => r) ->
    HRecWitness h n ->
    r
(##>>) _ r HRecSelf = r \\ recursively (Proxy @(c h))
(##>>) _ r (HRecSub (w0 :: HRecWitness h p) w1) =
    ( Proxy @(Recursively c)
        #>> ( (Proxy @(Recursively c) #> (r \\ recursively (Proxy @(c n)))) w1
                \\ recursively (Proxy @(c p))
            )
    )
        w0

-- | A variant of '#>>' which does not consume the witness parameter.
--
-- @Proxy @c0 #**# Proxy @c1 #>> r@ brings into context both the @c0 n@ and @c1 n@ constraints.
{-# INLINE (#**#) #-}
(#**#) ::
    (Recursive c, c h, RNodes h) =>
    Proxy c ->
    (c n => HRecWitness h n -> r) ->
    HRecWitness h n ->
    r
(#**#) p r w = (p #>> r) w w
