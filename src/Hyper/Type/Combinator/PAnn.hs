{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module Hyper.Type.Combinator.PAnn
    ( PAnn(..), pAnn, pVal
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

data PAnn a h = PAnn
    { _pAnn :: a h
    , _pVal :: h # PAnn a
    } deriving Generic
makeLenses ''PAnn

makeHTraversableApplyAndBases ''PAnn
makeCommonInstances [''PAnn]

instance RNodes h => HNodes (Flip PAnn h) where
    type HNodesConstraint (Flip PAnn h) c = (Recursive c, c h)
    type HWitnessType (Flip PAnn h) = HRecWitness h
    hLiftConstraint (HWitness HRecSelf) = const id
    hLiftConstraint (HWitness (HRecSub w0 w1)) = hLiftConstraintH w0 w1

-- TODO: Dedup this and similar code in Hyper.Unify.Generalize
hLiftConstraintH ::
    forall a c b n r.
    (RNodes a, HNodesConstraint (Flip PAnn a) c) =>
    HWitness a b -> HRecWitness b n -> Proxy c -> (c n => r) -> r
hLiftConstraintH c n =
    withDict (recurse (Proxy @(RNodes a))) $
    withDict (recurse (Proxy @(c a))) $
    hLiftConstraint c (Proxy @RNodes)
    ( hLiftConstraint c (Proxy @c)
        (hLiftConstraint (HWitness @(Flip PAnn _) n))
    )

instance Recursively HFunctor h => HFunctor (Flip PAnn h) where
    hmap f =
        withDict (recursively (Proxy @(HFunctor h))) $
        _Flip %~
        \(PAnn a b) ->
        PAnn
        (f (HWitness HRecSelf) a)
        (hmap
            ( Proxy @(Recursively HFunctor) #*#
                \w -> from _Flip %~ hmap (f . HWitness . HRecSub w . (^. _HWitness))
            ) b
        )

instance Recursively HFoldable h => HFoldable (Flip PAnn h) where
    hfoldMap f (MkFlip (PAnn a b)) =
        withDict (recursively (Proxy @(HFoldable h))) $
        f (HWitness HRecSelf) a <>
        hfoldMap
        ( Proxy @(Recursively HFoldable) #*#
            \w -> hfoldMap (f . HWitness . HRecSub w . (^. _HWitness)) . MkFlip
        ) b

instance RTraversable h => HTraversable (Flip PAnn h) where
    hsequence =
        withDict (recurse (Proxy @(RTraversable h))) $
        _Flip
        ( \(PAnn a b) ->
            PAnn
            <$> runContainedH a
            <*> htraverse (Proxy @RTraversable #> from _Flip hsequence) b
        )
