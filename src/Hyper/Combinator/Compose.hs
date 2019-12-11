-- | Compose two 'HyperType's.
--
-- Inspired by [hyperfunctions' @Category@ instance](http://hackage.haskell.org/package/hyperfunctions-0/docs/Control-Monad-Hyper.html).

{-# LANGUAGE UndecidableInstances, FlexibleInstances, TemplateHaskell #-}

module Hyper.Combinator.Compose
    ( HCompose(..), _HCompose, W_HCompose(..)
    , HComposeConstraint1
    ) where

import Control.Lens (iso)
import Hyper.Class.Apply (HApply(..))
import Hyper.Class.Context (HContext(..))
import Hyper.Class.Foldable (HFoldable(..))
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..), HWitness(..))
import Hyper.Class.Pointed (HPointed(..))
import Hyper.Class.Traversable (HTraversable(..), ContainedH(..), htraverse)
import Hyper.Class.Recursive (RNodes(..), Recursively(..), RTraversable)
import Hyper.Class.ZipMatch (ZipMatch(..))
import Hyper.Combinator.Func (HFunc(..))
import Hyper.Type (HyperType, GetHyperType, type (#))

import Hyper.Internal.Prelude

-- | Compose two 'HyperType's as an external and internal layer
newtype HCompose a b h = HCompose { getHCompose :: a # HCompose b (GetHyperType h) }
    deriving stock Generic

makeCommonInstances [''HCompose]

-- | An 'Control.Lens.Iso' for the 'HCompose' @newtype@
{-# INLINE _HCompose #-}
_HCompose ::
    Iso
    (HCompose a0 b0 # h0) (HCompose a1 b1 # h1)
    (a0 # HCompose b0 h0) (a1 # HCompose b1 h1)
_HCompose = iso getHCompose HCompose

data W_HCompose a b n where
    W_HCompose :: HWitness a a0 -> HWitness b b0 -> W_HCompose a b (HCompose a0 b0)

instance (HNodes a, HNodes b) => HNodes (HCompose a b) where
    type HNodesConstraint (HCompose a b) c = HNodesConstraint a (HComposeConstraint0 c b)
    type HWitnessType (HCompose a b) = W_HCompose a b
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (HWitness (W_HCompose w0 w1)) p r =
        hLiftConstraint w0 (p0 p) $
        withDict (hComposeConstraint0 p (Proxy @b) w0) $
        hLiftConstraint w1 (p1 p w0) $
        withDict (d0 p w0 w1) r
        where
            p0 :: Proxy c -> Proxy (HComposeConstraint0 c b)
            p0 _ = Proxy
            p1 :: proxy0 c -> proxy1 a0 -> Proxy (HComposeConstraint1 c a0)
            p1 _ _ = Proxy
            d0 ::
                HComposeConstraint1 c a0 b0 =>
                Proxy c -> HWitness a a0 -> HWitness b b0 -> Dict (c (HCompose a0 b0))
            d0 _ _ _ = hComposeConstraint1

class HComposeConstraint0 (c :: HyperType -> Constraint) (b :: HyperType) (h0 :: HyperType) where
    hComposeConstraint0 ::
        proxy0 c -> proxy1 b -> proxy2 h0 ->
        Dict (HNodesConstraint b (HComposeConstraint1 c h0))

instance HNodesConstraint b (HComposeConstraint1 c h0) => HComposeConstraint0 c b h0 where
    {-# INLINE hComposeConstraint0 #-}
    hComposeConstraint0 _ _ _ = Dict

class HComposeConstraint1 (c :: HyperType -> Constraint) (h0 :: HyperType) (h1 :: HyperType) where
    hComposeConstraint1 :: Dict (c (HCompose h0 h1))

instance c (HCompose h0 h1) => HComposeConstraint1 c h0 h1 where
    {-# INLINE hComposeConstraint1 #-}
    hComposeConstraint1 = Dict

instance
    (HNodes a, HPointed a, HPointed b) =>
    HPointed (HCompose a b) where
    {-# INLINE hpure #-}
    hpure x =
        _HCompose #
        hpure
        ( \wa ->
            _HCompose # hpure (\wb -> _HCompose # x (HWitness (W_HCompose wa wb)))
        )

instance (HFunctor a, HFunctor b) => HFunctor (HCompose a b) where
    {-# INLINE hmap #-}
    hmap f =
        _HCompose %~
        hmap
        ( \w0 ->
            _HCompose %~ hmap (\w1 -> _HCompose %~ f (HWitness (W_HCompose w0 w1)))
        )

instance (HApply a, HApply b) => HApply (HCompose a b) where
    {-# INLINE hzip #-}
    hzip (HCompose a0) =
        _HCompose %~
        hmap
        ( \_ (HCompose b0 :*: HCompose b1) ->
            _HCompose #
            hmap
            ( \_ (HCompose i0 :*: HCompose i1) ->
                _HCompose # (i0 :*: i1)
            ) (hzip b0 b1)
        )
        . hzip a0

instance (HFoldable a, HFoldable b) => HFoldable (HCompose a b) where
    {-# INLINE hfoldMap #-}
    hfoldMap f =
        hfoldMap
        ( \w0 ->
            hfoldMap (\w1 -> f (HWitness (W_HCompose w0 w1)) . (^. _HCompose)) . (^. _HCompose)
        ) . (^. _HCompose)

instance (HTraversable a, HTraversable b) => HTraversable (HCompose a b) where
    {-# INLINE hsequence #-}
    hsequence =
        _HCompose
        ( hsequence .
            hmap (const (MkContainedH . _HCompose (htraverse (const (_HCompose runContainedH)))))
        )

instance
    (ZipMatch h0, ZipMatch h1, HTraversable h0, HFunctor h1) =>
    ZipMatch (HCompose h0 h1) where
    {-# INLINE zipMatch #-}
    zipMatch (HCompose x) (HCompose y) =
        zipMatch x y
        >>= htraverse
            (\_ (HCompose cx :*: HCompose cy) ->
                zipMatch cx cy
                <&> hmap
                    (\_ (HCompose bx :*: HCompose by) -> bx :*: by & HCompose)
                <&> (_HCompose #)
            )
        <&> (_HCompose #)

instance (HFunctor h0, HContext h0, HFunctor h1, HContext h1) => HContext (HCompose h0 h1) where
    hcontext =
        _HCompose %~
        hmap
        ( \_ (HFunc c0 :*: x0) ->
            x0 & _HCompose %~
            hmap
            ( \_ (HFunc c1 :*: x1) ->
                x1 & _HCompose %~
                (HFunc (Const . (_HCompose #) . getConst . c0 . (_HCompose #) . getConst . c1 . (_HCompose #)) :*:)
            ) . hcontext
        ) . hcontext

instance
    ( HNodes a, HNodes b
    , HNodesConstraint a (HComposeConstraint0 RNodes b)
    ) => RNodes (HCompose a b)

instance
    ( HNodes h0, HNodes h1
    , c (HCompose h0 h1)
    , HNodesConstraint h0 (HComposeConstraint0 RNodes h1)
    , HNodesConstraint h0 (HComposeConstraint0 (Recursively c) h1)
    ) => Recursively c (HCompose h0 h1)

instance
    ( HTraversable a, HTraversable b
    , HNodesConstraint a (HComposeConstraint0 RNodes b)
    , HNodesConstraint a (HComposeConstraint0 (Recursively HFunctor) b)
    , HNodesConstraint a (HComposeConstraint0 (Recursively HFoldable) b)
    , HNodesConstraint a (HComposeConstraint0 RTraversable b)
    ) => RTraversable (HCompose a b)
