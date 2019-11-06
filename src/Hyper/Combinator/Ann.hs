{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module Hyper.Combinator.Ann
    ( Ann(..), hAnn, hVal
    , Annotated, annotation
    ) where

import Control.Lens (Lens', _Wrapped, makeLenses, from)
import Control.Lens.Operators
import Data.Constraint
import Data.Functor.Const (Const)
import Data.Proxy
import GHC.Generics (Generic)
import Hyper.Class.Foldable
import Hyper.Class.Functor
import Hyper.Class.Nodes
import Hyper.Class.Traversable
import Hyper.Combinator.Flip
import Hyper.Recurse
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (type (#), Tree)

import Prelude.Compat

data Ann a h = Ann
    { _hAnn :: a h
    , _hVal :: h # Ann a
    } deriving Generic
makeLenses ''Ann

makeHTraversableApplyAndBases ''Ann
makeCommonInstances [''Ann]

instance RNodes h => HNodes (HFlip Ann h) where
    type HNodesConstraint (HFlip Ann h) c = (Recursive c, c h)
    type HWitnessType (HFlip Ann h) = HRecWitness h
    hLiftConstraint (HWitness HRecSelf) = const id
    hLiftConstraint (HWitness (HRecSub w0 w1)) = hLiftConstraintH w0 w1

-- TODO: Dedup this and similar code in Hyper.Unify.Generalize
hLiftConstraintH ::
    forall a c b n r.
    (RNodes a, HNodesConstraint (HFlip Ann a) c) =>
    HWitness a b -> HRecWitness b n -> Proxy c -> (c n => r) -> r
hLiftConstraintH c n =
    withDict (recurse (Proxy @(RNodes a))) $
    withDict (recurse (Proxy @(c a))) $
    hLiftConstraint c (Proxy @RNodes)
    ( hLiftConstraint c (Proxy @c)
        (hLiftConstraint (HWitness @(HFlip Ann _) n))
    )

type Annotated a h = Tree (Ann (Const a)) h

annotation :: Lens' (Ann (Const a) h) a
annotation = hAnn . _Wrapped

instance RNodes a => RNodes (Ann a) where
    {-# INLINE recursiveHNodes #-}
    recursiveHNodes _ = withDict (recursiveHNodes (Proxy @a)) Dict

instance (c (Ann a), Recursively c a) => Recursively c (Ann a) where
    {-# INLINE recursively #-}
    recursively _ = withDict (recursively (Proxy @(c a))) Dict

instance RTraversable a => RTraversable (Ann a) where
    {-# INLINE recursiveHTraversable #-}
    recursiveHTraversable _ = withDict (recursiveHTraversable (Proxy @a)) Dict

instance Recursively HFunctor h => HFunctor (HFlip Ann h) where
    {-# INLINE hmap #-}
    hmap f =
        withDict (recursively (Proxy @(HFunctor h))) $
        _HFlip %~
        \(Ann a b) ->
        Ann
        (f (HWitness HRecSelf) a)
        (hmap
            ( Proxy @(Recursively HFunctor) #*#
                \w -> from _HFlip %~ hmap (f . HWitness . HRecSub w . (^. _HWitness))
            ) b
        )

instance Recursively HFoldable h => HFoldable (HFlip Ann h) where
    {-# INLINE hfoldMap #-}
    hfoldMap f (MkHFlip (Ann a b)) =
        withDict (recursively (Proxy @(HFoldable h))) $
        f (HWitness HRecSelf) a <>
        hfoldMap
        ( Proxy @(Recursively HFoldable) #*#
            \w -> hfoldMap (f . HWitness . HRecSub w . (^. _HWitness)) . MkHFlip
        ) b

instance RTraversable h => HTraversable (HFlip Ann h) where
    {-# INLINE hsequence #-}
    hsequence =
        withDict (recurse (Proxy @(RTraversable h))) $
        _HFlip
        ( \(Ann a b) ->
            Ann
            <$> runContainedH a
            <*> htraverse (Proxy @RTraversable #> from _HFlip hsequence) b
        )
