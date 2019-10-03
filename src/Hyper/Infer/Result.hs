{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}

module Hyper.Infer.Result
    ( InferResult(..), _InferResult
    ) where

import Control.Lens (makePrisms)
import GHC.Generics (Generic)
import Hyper
import Hyper.Class.Infer
import Hyper.TH.Internal.Instances (makeCommonInstances)

-- | A 'HyperType' for an inferred term - the output of 'Hyper.Infer.infer'
newtype InferResult v e =
    InferResult (Tree (InferOf (GetHyperType e)) v)
    deriving Generic
makePrisms ''InferResult
makeCommonInstances [''InferResult]
