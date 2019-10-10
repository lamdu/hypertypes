{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module Hyper.Combinator.Ann
    ( Ann(..), ann, val
    ) where

import Control.Lens (makeLenses, from)
import Control.Lens.Operators
import Data.Constraint
import Data.Proxy
import GHC.Generics (Generic)
import Hyper.Class.Nodes
import Hyper.Class.Functor
import Hyper.Class.Foldable
import Hyper.Class.Traversable
import Hyper.Combinator.Flip
import Hyper.Recurse
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (type (#))

import Prelude.Compat

data Ann a h = Ann
    { _ann :: a h
    , _val :: h # Ann a
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

instance Recursively HFunctor h => HFunctor (HFlip Ann h) where
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
    hfoldMap f (MkHFlip (Ann a b)) =
        withDict (recursively (Proxy @(HFoldable h))) $
        f (HWitness HRecSelf) a <>
        hfoldMap
        ( Proxy @(Recursively HFoldable) #*#
            \w -> hfoldMap (f . HWitness . HRecSub w . (^. _HWitness)) . MkHFlip
        ) b

instance RTraversable h => HTraversable (HFlip Ann h) where
    hsequence =
        withDict (recurse (Proxy @(RTraversable h))) $
        _HFlip
        ( \(Ann a b) ->
            Ann
            <$> runContainedH a
            <*> htraverse (Proxy @RTraversable #> from _HFlip hsequence) b
        )
