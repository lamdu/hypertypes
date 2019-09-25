-- | Compose two 'HyperType's.
--
-- Inspired by [hyperfunctions' @Category@ instance](http://hackage.haskell.org/package/hyperfunctions-0/docs/Control-Monad-Hyper.html).

{-# LANGUAGE UndecidableSuperClasses, UndecidableInstances, FlexibleInstances, TemplateHaskell #-}

module Hyper.Type.Combinator.Compose
    ( Compose(..), _Compose
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Functor.Product.PolyKinds (Product(..))
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
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
newtype Compose a b h = MkCompose { getCompose :: Tree a (Compose b (GetHyperType h)) }
    deriving stock Generic

makeCommonInstances [''Compose]

-- | An 'Control.Lens.Iso' for the 'Compose' @newtype@
{-# INLINE _Compose #-}
_Compose ::
    Lens.Iso
    (Tree (Compose a0 b0) k0) (Tree (Compose a1 b1) k1)
    (Tree a0 (Compose b0 k0)) (Tree a1 (Compose b1 k1))
_Compose = Lens.iso getCompose MkCompose

instance (HNodes a, HNodes b) => HNodes (Compose a b) where
    type HNodesConstraint (Compose a b) c = HNodesConstraint a (ComposeConstraint0 c b)
    data HWitness (Compose a b) n where
        HWitness_Compose :: HWitness a a0 -> HWitness b b0 -> HWitness (Compose a b) (Compose a0 b0)
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (HWitness_Compose w0 w1) p r =
        kLiftConstraint w0 (p0 p) (kLiftConstraint w1 (p1 p w0) r)
        where
            p0 :: Proxy c -> Proxy (ComposeConstraint0 c b)
            p0 _ = Proxy
            p1 :: Proxy c -> HWitness a a0 -> Proxy (ComposeConstraint1 c a0)
            p1 _ _ = Proxy

-- TODO: Avoid UndecidableSuperClasses!

class    HNodesConstraint b (ComposeConstraint1 c k0) => ComposeConstraint0 c b k0
instance HNodesConstraint b (ComposeConstraint1 c k0) => ComposeConstraint0 c b k0
class    c (Compose k0 k1) => ComposeConstraint1 c k0 k1
instance c (Compose k0 k1) => ComposeConstraint1 c k0 k1

instance
    (HNodes a, HPointed a, HPointed b) =>
    HPointed (Compose a b) where
    {-# INLINE pureH #-}
    pureH x =
        _Compose #
        pureH
        ( \wa ->
            _Compose # pureH (\wb -> _Compose # x (HWitness_Compose wa wb))
        )

instance (HFunctor a, HFunctor b) => HFunctor (Compose a b) where
    {-# INLINE mapH #-}
    mapH f =
        _Compose %~
        mapH
        ( \w0 ->
            _Compose %~ mapH (\w1 -> _Compose %~ f (HWitness_Compose w0 w1))
        )

instance (HApply a, HApply b) => HApply (Compose a b) where
    {-# INLINE zipH #-}
    zipH (MkCompose a0) =
        _Compose %~
        mapH
        ( \_ (Pair (MkCompose b0) (MkCompose b1)) ->
            _Compose #
            mapH
            ( \_ (Pair (MkCompose i0) (MkCompose i1)) ->
                _Compose # Pair i0 i1
            ) (zipH b0 b1)
        )
        . zipH a0

instance (HFoldable a, HFoldable b) => HFoldable (Compose a b) where
    {-# INLINE foldMapH #-}
    foldMapH f =
        foldMapH
        ( \w0 ->
            foldMapH (\w1 -> f (HWitness_Compose w0 w1) . (^. _Compose)) . (^. _Compose)
        ) . (^. _Compose)

instance (HTraversable a, HTraversable b) => HTraversable (Compose a b) where
    {-# INLINE sequenceH #-}
    sequenceH =
        _Compose
        ( sequenceH .
            mapH (const (MkContainedH . _Compose (traverseH (const (_Compose runContainedH)))))
        )

instance
    (ZipMatch k0, ZipMatch k1, HTraversable k0, HFunctor k1) =>
    ZipMatch (Compose k0 k1) where
    {-# INLINE zipMatch #-}
    zipMatch (MkCompose x) (MkCompose y) =
        zipMatch x y
        >>= traverseH
            (\_ (Pair (MkCompose cx) (MkCompose cy)) ->
                zipMatch cx cy
                <&> mapH
                    (\_ (Pair (MkCompose bx) (MkCompose by)) -> Pair bx by & MkCompose)
                <&> (_Compose #)
            )
        <&> (_Compose #)
