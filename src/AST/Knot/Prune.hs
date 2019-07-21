{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds, UndecidableInstances #-}

module AST.Knot.Prune
    ( Prune(..)
    ) where

import AST
import AST.Class.Applicative (LiftK2(..))
import AST.Class.HasChildrenTypes (HasChildrenTypes)
import AST.Class.Pointed (KPointed(..))
import AST.Class.Traversable.TH (makeKTraversableAndBases)
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
    Pruned | Unpruned (Tie k Prune)
    deriving Generic

type instance ChildrenTypesOf Prune = Single Prune
instance HasChildrenTypes Prune

makePrisms ''Prune
makeChildren ''Prune
makeKTraversableAndBases ''Prune
makeZipMatch ''Prune

-- `KPointed` and `KApplicative` instances in the spirit of `Maybe`

instance KPointed Prune where
    type KLiftConstraint Prune c = c Prune
    pureC (MkSingle x) = Unpruned x
    pureK = Unpruned
    pureKWith _ = Unpruned

instance KApplicative Prune where
    liftC2 _ Pruned _ = Pruned
    liftC2 _ _ Pruned = Pruned
    liftC2 (MkSingle (MkLiftK2 f)) (Unpruned x) (Unpruned y) = f x y & Unpruned

instance c Prune => Recursive c Prune

type instance TypeOf  (Compose Prune t) = TypeOf  t
type instance ScopeOf (Compose Prune t) = ScopeOf t

instance
    ( Infer m t
    , KFunctor t, HasChildrenTypes t
    ) =>
    Infer m (Compose Prune t) where
    inferBody (MkCompose Pruned) = newUnbound <&> InferRes (MkCompose Pruned)
    inferBody (MkCompose (Unpruned (MkCompose x))) =
        mapK
        (\(MkCompose (InferChild i)) -> i <&> inRep %~ MkCompose & InferChild)
        x
        & inferBody
        <&> inferResBody %~ MkCompose . Unpruned . MkCompose

deriving instance Eq   (Tie k Prune) => Eq   (Prune k)
deriving instance Ord  (Tie k Prune) => Ord  (Prune k)
deriving instance Show (Tie k Prune) => Show (Prune k)
instance Binary (Tie k Prune) => Binary (Prune k)
instance NFData (Tie k Prune) => NFData (Prune k)
