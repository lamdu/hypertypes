{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Hyper.Type.Prune
    ( Prune (..)
    , W_Prune (..)
    , _Pruned
    , _Unpruned
    ) where

import Hyper
import qualified Text.PrettyPrint as Pretty
import Text.PrettyPrint.HughesPJClass (Pretty (..))

import Hyper.Internal.Prelude

data Prune h
    = Pruned
    | Unpruned (h :# Prune)
    deriving (Generic)

instance Pretty (h :# Prune) => Pretty (Prune h) where
    pPrintPrec _ _ Pruned = Pretty.text "<pruned>"
    pPrintPrec level prec (Unpruned x) = pPrintPrec level prec x

makeCommonInstances [''Prune]
makePrisms ''Prune
makeHTraversableAndBases ''Prune
makeZipMatch ''Prune
makeHContext ''Prune

-- `HPointed` and `HApplicative` instances in the spirit of `Maybe`

instance HPointed Prune where
    hpure f = Unpruned (f (HWitness W_Prune_Prune))

instance HApply Prune where
    hzip Pruned _ = Pruned
    hzip _ Pruned = Pruned
    hzip (Unpruned x) (Unpruned y) = x :*: y & Unpruned

instance RNodes Prune
instance c Prune => Recursively c Prune
instance RTraversable Prune
