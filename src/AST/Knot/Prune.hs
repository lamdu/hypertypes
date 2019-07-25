{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds, UndecidableInstances #-}

module AST.Knot.Prune
    ( Prune(..)
    ) where

import AST
import AST.Class.Traversable.TH (makeKTraversableAndBases)
import AST.Combinator.Both (Both(..))
import AST.Combinator.Compose (Compose(..))
import AST.Combinator.Single (Single(..))
import AST.Infer
import AST.Unify.New (newUnbound)
import Control.DeepSeq (NFData)
import Control.Lens (makePrisms)
import Control.Lens.Operators
import Data.Binary (Binary)
import GHC.Generics (Generic)

import Prelude.Compat

data Prune k =
    Pruned | Unpruned (Node k Prune)
    deriving Generic

instance HasNodes Prune where
    type NodeTypesOf Prune = Single Prune

makePrisms ''Prune
makeKTraversableAndBases ''Prune
makeZipMatch ''Prune

-- `KPointed` and `KApplicative` instances in the spirit of `Maybe`

instance KPointed Prune where
    pureC (MkSingle x) = Unpruned x
    pureK = Unpruned
    pureKWithConstraint _ = Unpruned

instance KApply Prune where
    zipK Pruned _ = Pruned
    zipK _ Pruned = Pruned
    zipK (Unpruned x) (Unpruned y) = Both x y & Unpruned

instance c Prune => Recursive c Prune

type instance TypeOf  (Compose Prune t) = TypeOf  t
type instance ScopeOf (Compose Prune t) = ScopeOf t

instance
    (Infer m t, KFunctor t) =>
    Infer m (Compose Prune t) where
    inferBody (MkCompose Pruned) = newUnbound <&> InferRes (MkCompose Pruned)
    inferBody (MkCompose (Unpruned (MkCompose x))) =
        mapK
        (\(MkCompose (InferChild i)) -> i <&> inRep %~ MkCompose & InferChild)
        x
        & inferBody
        <&> inferResBody %~ MkCompose . Unpruned . MkCompose

deriving instance Eq   (Node k Prune) => Eq   (Prune k)
deriving instance Ord  (Node k Prune) => Ord  (Prune k)
deriving instance Show (Node k Prune) => Show (Prune k)
instance Binary (Node k Prune) => Binary (Prune k)
instance NFData (Node k Prune) => NFData (Prune k)
