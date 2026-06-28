{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Hyper.Combinator.Ann
    ( Ann (..)
    , hAnn
    , hVal
    , Annotated
    , annotation
    , annValue
    ) where

import Control.Lens (Lens, Lens', from, _Wrapped)
import Hyper.Class.Foldable (HFoldable (..))
import Hyper.Class.Functor (HFunctor (..))
import Hyper.Class.Nodes
import Hyper.Class.Traversable
import Hyper.Combinator.Flip
import Hyper.Recurse
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (type (#), type (:#))

import Hyper.Internal.Prelude

data Ann a h = Ann
    { _hAnn :: a h
    , _hVal :: h :# Ann a
    }
    deriving (Generic)
makeLenses ''Ann

makeHTraversableApplyAndBases ''Ann
makeCommonInstances [''Ann]

instance RNodes h => HNodes (HFlip Ann h) where
    type HNodesConstraint (HFlip Ann h) c = (Recursive c, c h)
    type HWitnessType (HFlip Ann h) = HRecWitness h
    hLiftConstraint = recursiveHLiftConstraint

instance RNodes a => RNodes (Ann a) where
    {-# INLINE recursiveHNodes #-}
    recursiveHNodes _ = Dict \\ recursiveHNodes (Proxy @a)

instance (c (Ann a), Recursively c a) => Recursively c (Ann a) where
    {-# INLINE recursively #-}
    recursively _ = Dict \\ recursively (Proxy @(c a))

instance RTraversable a => RTraversable (Ann a) where
    {-# INLINE recursiveHTraversable #-}
    recursiveHTraversable _ = Dict \\ recursiveHTraversable (Proxy @a)

instance Recursively HFunctor h => HFunctor (HFlip Ann h) where
    {-# INLINE hmap #-}
    hmap (f :: forall n. HWitness (HFlip Ann h) n -> p # n -> q # n) (MkHFlip (Ann a b)) =
        MkHFlip (Ann (f (HWitness HRecSelf) a) (go HRecSelf b))
        where
            go :: forall c. Recursively HFunctor c => HRecWitness h c -> c # Ann p -> c # Ann q
            go prefix =
                hmap
                    ( Proxy @(Recursively HFunctor) #*# \w (Ann a' b') ->
                        Ann (f (HWitness (HRecSub prefix w)) a') (go (HRecSub prefix w) b')
                    )
                    \\ recursively (Proxy @(HFunctor c))

instance Recursively HFoldable h => HFoldable (HFlip Ann h) where
    {-# INLINE hfoldMap #-}
    hfoldMap (f :: forall n. HWitness (HFlip Ann h) n -> p # n -> a) (MkHFlip (Ann a b)) =
        f (HWitness HRecSelf) a <> go HRecSelf b
        where
            go :: forall c. Recursively HFoldable c => HRecWitness h c -> c # Ann p -> a
            go prefix =
                hfoldMap
                    ( Proxy @(Recursively HFoldable) #*# \w (Ann a' b') ->
                        f (HWitness (HRecSub prefix w)) a' <> go (HRecSub prefix w) b'
                    )
                    \\ recursively (Proxy @(HFoldable c))

instance RTraversable h => HTraversable (HFlip Ann h) where
    {-# INLINE hsequence #-}
    hsequence =
        _HFlip
            ( \(Ann a b) ->
                Ann
                    <$> runContainedH a
                    <*> htraverse (Proxy @RTraversable #> from _HFlip hsequence) b
                    \\ recurse (Proxy @(RTraversable h))
            )

type Annotated a = Ann (Const a)

annotation :: Lens' (Annotated a # h) a
annotation = hAnn . _Wrapped

-- | Polymorphic lens to an @Annotated@ value
annValue :: Lens (Annotated a # h0) (Annotated a # h1) (h0 # Annotated a) (h1 # Annotated a)
annValue f (Ann (Const a) b) = f b <&> Ann (Const a)
