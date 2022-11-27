{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances, FlexibleContexts #-}

module Hyper.Combinator.Ann
    ( Ann(..), hAnn, hVal
    , Annotated, annotation, annValue
    ) where

import Control.Lens (Lens, Lens', _Wrapped, from)
import Hyper.Class.Foldable (HFoldable(..))
import Hyper.Class.Functor (HFunctor(..))
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
    } deriving Generic
makeLenses ''Ann

makeHTraversableApplyAndBases ''Ann
makeCommonInstances [''Ann]

instance RNodes h => HNodes (HFlip Ann h) where
    type HNodesConstraint (HFlip Ann h) c = (Recursive c, c h)
    type HWitnessType (HFlip Ann h) = HRecWitness h
    hLiftConstraint (HWitness HRecSelf) = \_ x -> x
    hLiftConstraint (HWitness (HRecSub w0 w1)) = hLiftConstraintH w0 w1

-- TODO: Dedup this and similar code in Hyper.Unify.Generalize
hLiftConstraintH ::
    forall a c b n r.
    (RNodes a, HNodesConstraint (HFlip Ann a) c) =>
    HWitness a b -> HRecWitness b n -> Proxy c -> (c n => r) -> r
hLiftConstraintH c n p f =
    hLiftConstraint c (Proxy @RNodes)
    ( hLiftConstraint c p
        (hLiftConstraint (HWitness @(HFlip Ann _) n) p f)
        \\ recurse (Proxy @(c a))
    )
    \\ recurse (Proxy @(RNodes a))

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
    hmap f =
        _HFlip %~
        \(Ann a b) ->
        Ann
        (f (HWitness HRecSelf) a)
        (hmap
            ( Proxy @(Recursively HFunctor) #*#
                \w -> from _HFlip %~ hmap (f . HWitness . HRecSub w . (^. _HWitness))
            ) b
            \\ recursively (Proxy @(HFunctor h))
        )

instance Recursively HFoldable h => HFoldable (HFlip Ann h) where
    {-# INLINE hfoldMap #-}
    hfoldMap f (MkHFlip (Ann a b)) =
        f (HWitness HRecSelf) a <>
        hfoldMap
        ( Proxy @(Recursively HFoldable) #*#
            \w -> hfoldMap (f . HWitness . HRecSub w . (^. _HWitness)) . MkHFlip
        ) b
        \\ recursively (Proxy @(HFoldable h))

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
