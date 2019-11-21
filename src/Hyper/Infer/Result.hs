{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module Hyper.Infer.Result
    ( InferResult(..), _InferResult
    ) where

import Control.Lens (makePrisms)
import Control.Lens.Operators
import GHC.Generics (Generic)
import Hyper
import Hyper.Class.Infer
import Hyper.TH.Internal.Instances (makeCommonInstances)

import Prelude.Compat

-- | A 'HyperType' for an inferred term - the output of 'Hyper.Infer.infer'
newtype InferResult v e =
    InferResult (Tree (InferOf (GetHyperType e)) v)
    deriving stock Generic
makePrisms ''InferResult
makeCommonInstances [''InferResult]

instance HNodes (InferOf e) => HNodes (HFlip InferResult e) where
    type HNodesConstraint (HFlip InferResult e) c = HNodesConstraint (InferOf e) c
    type HWitnessType (HFlip InferResult e) = HWitnessType (InferOf e)
    hLiftConstraint (HWitness w) = hLiftConstraint (HWitness @(InferOf e) w)

instance HFunctor (InferOf e) => HFunctor (HFlip InferResult e) where
    hmap f = _HFlip . _InferResult %~ hmap (f . HWitness . (^. _HWitness))

instance HFoldable (InferOf e) => HFoldable (HFlip InferResult e) where
    hfoldMap f = hfoldMap (f . HWitness . (^. _HWitness)) . (^. _HFlip . _InferResult)

instance HTraversable (InferOf e) => HTraversable (HFlip InferResult e) where
    hsequence = (_HFlip . _InferResult) hsequence
