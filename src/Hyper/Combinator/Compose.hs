-- | Compose two 'HyperType's.
--
-- Inspired by [hyperfunctions' @Category@ instance](http://hackage.haskell.org/package/hyperfunctions-0/docs/Control-Monad-Hyper.html).

{-# LANGUAGE UndecidableSuperClasses, UndecidableInstances, FlexibleInstances, TemplateHaskell #-}

module Hyper.Combinator.Compose
    ( HCompose(..), _HCompose, W_HCompose(..)
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic, (:*:)(..))
import           Hyper.Class.Apply
import           Hyper.Class.Foldable
import           Hyper.Class.Functor
import           Hyper.Class.Nodes
import           Hyper.Class.Pointed
import           Hyper.Class.Traversable
import           Hyper.Class.ZipMatch (ZipMatch(..))
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Type

import           Prelude.Compat

-- | Compose two 'HyperType's as an external and internal layer
newtype HCompose a b h = MkHCompose { getHCompose :: Tree a (HCompose b (GetHyperType h)) }
    deriving stock Generic

makeCommonInstances [''HCompose]

-- | An 'Control.Lens.Iso' for the 'HCompose' @newtype@
{-# INLINE _HCompose #-}
_HCompose ::
    Lens.Iso
    (Tree (HCompose a0 b0) k0) (Tree (HCompose a1 b1) k1)
    (Tree a0 (HCompose b0 k0)) (Tree a1 (HCompose b1 k1))
_HCompose = Lens.iso getHCompose MkHCompose

data W_HCompose a b n where
    W_HCompose :: HWitness a a0 -> HWitness b b0 -> W_HCompose a b (HCompose a0 b0)

instance (HNodes a, HNodes b) => HNodes (HCompose a b) where
    type HNodesConstraint (HCompose a b) c = HNodesConstraint a (HComposeConstraint0 c b)
    type HWitnessType (HCompose a b) = W_HCompose a b
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (HWitness (W_HCompose w0 w1)) p r =
        hLiftConstraint w0 (p0 p)
        (hLiftConstraint w1 (p1 p w0) r)
        where
            p0 :: Proxy c -> Proxy (HComposeConstraint0 c b)
            p0 _ = Proxy
            p1 :: Proxy c -> HWitness a a0 -> Proxy (HComposeConstraint1 c a0)
            p1 _ _ = Proxy

-- TODO: Avoid UndecidableSuperClasses!

class    HNodesConstraint b (HComposeConstraint1 c k0) => HComposeConstraint0 c b k0
instance HNodesConstraint b (HComposeConstraint1 c k0) => HComposeConstraint0 c b k0
class    c (HCompose k0 k1) => HComposeConstraint1 c k0 k1
instance c (HCompose k0 k1) => HComposeConstraint1 c k0 k1

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
    hzip (MkHCompose a0) =
        _HCompose %~
        hmap
        ( \_ (MkHCompose b0 :*: MkHCompose b1) ->
            _HCompose #
            hmap
            ( \_ (MkHCompose i0 :*: MkHCompose i1) ->
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
    (ZipMatch k0, ZipMatch k1, HTraversable k0, HFunctor k1) =>
    ZipMatch (HCompose k0 k1) where
    {-# INLINE zipMatch #-}
    zipMatch (MkHCompose x) (MkHCompose y) =
        zipMatch x y
        >>= htraverse
            (\_ (MkHCompose cx :*: MkHCompose cy) ->
                zipMatch cx cy
                <&> hmap
                    (\_ (MkHCompose bx :*: MkHCompose by) -> bx :*: by & MkHCompose)
                <&> (_HCompose #)
            )
        <&> (_HCompose #)