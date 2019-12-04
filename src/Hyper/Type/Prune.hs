{-# LANGUAGE UndecidableInstances, ScopedTypeVariables, TemplateHaskell, FlexibleInstances #-}

module Hyper.Type.Prune
    ( Prune(..), W_Prune(..), _Pruned, _Unpruned
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Hyper
import           Hyper.Class.Traversable
import           Hyper.Class.Unify (UnifyGen)
import           Hyper.Combinator.Compose (HComposeConstraint1)
import           Hyper.Infer
import           Hyper.Infer.Blame (Blame(..))
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Unify.New (newUnbound)

import           Prelude.Compat

data Prune h =
    Pruned | Unpruned (h :# Prune)
    deriving Generic

makeCommonInstances [''Prune]
Lens.makePrisms ''Prune
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

type instance InferOf (HCompose Prune t) = InferOf t

instance
    ( Infer m t
    , HPointed (InferOf t)
    , HTraversable (InferOf t)
    , HNodesConstraint t (HComposeConstraint1 (Infer m) Prune)
    ) =>
    Infer m (HCompose Prune t) where
    inferBody (MkHCompose Pruned) =
        withDict (inferContext (Proxy @m) (Proxy @t)) $
        hpure (Proxy @(UnifyGen m) #> MkContainedH newUnbound)
        & hsequence
        <&> (MkHCompose Pruned, )
    inferBody (MkHCompose (Unpruned (MkHCompose x))) =
        hmap
        ( \_ (MkHCompose (InferChild i)) ->
            i <&> (\(InferredChild r t) -> InferredChild (MkHCompose r) t)
            & InferChild
        ) x
        & inferBody
        <&> Lens._1 %~ MkHCompose . Unpruned . MkHCompose
    inferContext m _ = withDict (inferContext m (Proxy @t)) Dict

instance
    ( Blame m t
    , HNodesConstraint t (HComposeConstraint1 (Infer m) Prune)
    , HNodesConstraint t (HComposeConstraint1 (Blame m) Prune)
    , HNodesConstraint t (HComposeConstraint1 RNodes Prune)
    , HNodesConstraint t (HComposeConstraint1 (Recursively HFunctor) Prune)
    , HNodesConstraint t (HComposeConstraint1 (Recursively HFoldable) Prune)
    , HNodesConstraint t (HComposeConstraint1 RTraversable Prune)
    ) =>
    Blame m (HCompose Prune t) where
    inferOfUnify _ = inferOfUnify (Proxy @t)
    inferOfMatches _ = inferOfMatches (Proxy @t)
