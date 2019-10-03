{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module Hyper.Type.Combinator.Ann
    ( Ann(..), pAnn, pVal
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
import Hyper.Recurse
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (type (#))
import Hyper.Type.Combinator.Flip

import Prelude.Compat

data Ann a h = Ann
    { _pAnn :: a h
    , _pVal :: h # Ann a
    } deriving Generic
makeLenses ''Ann

makeHTraversableApplyAndBases ''Ann
makeCommonInstances [''Ann]

instance RNodes h => HNodes (Flip Ann h) where
    type HNodesConstraint (Flip Ann h) c = (Recursive c, c h)
    type HWitnessType (Flip Ann h) = HRecWitness h
    hLiftConstraint (HWitness HRecSelf) = const id
    hLiftConstraint (HWitness (HRecSub w0 w1)) = hLiftConstraintH w0 w1

-- TODO: Dedup this and similar code in Hyper.Unify.Generalize
hLiftConstraintH ::
    forall a c b n r.
    (RNodes a, HNodesConstraint (Flip Ann a) c) =>
    HWitness a b -> HRecWitness b n -> Proxy c -> (c n => r) -> r
hLiftConstraintH c n =
    withDict (recurse (Proxy @(RNodes a))) $
    withDict (recurse (Proxy @(c a))) $
    hLiftConstraint c (Proxy @RNodes)
    ( hLiftConstraint c (Proxy @c)
        (hLiftConstraint (HWitness @(Flip Ann _) n))
    )

instance Recursively HFunctor h => HFunctor (Flip Ann h) where
    hmap f =
        withDict (recursively (Proxy @(HFunctor h))) $
        _Flip %~
        \(Ann a b) ->
        Ann
        (f (HWitness HRecSelf) a)
        (hmap
            ( Proxy @(Recursively HFunctor) #*#
                \w -> from _Flip %~ hmap (f . HWitness . HRecSub w . (^. _HWitness))
            ) b
        )

instance Recursively HFoldable h => HFoldable (Flip Ann h) where
    hfoldMap f (MkFlip (Ann a b)) =
        withDict (recursively (Proxy @(HFoldable h))) $
        f (HWitness HRecSelf) a <>
        hfoldMap
        ( Proxy @(Recursively HFoldable) #*#
            \w -> hfoldMap (f . HWitness . HRecSub w . (^. _HWitness)) . MkFlip
        ) b

instance RTraversable h => HTraversable (Flip Ann h) where
    hsequence =
        withDict (recurse (Proxy @(RTraversable h))) $
        _Flip
        ( \(Ann a b) ->
            Ann
            <$> runContainedH a
            <*> htraverse (Proxy @RTraversable #> from _Flip hsequence) b
        )
