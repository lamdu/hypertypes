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

import qualified Control.Lens as Lens
import Hyper
import Hyper.Class.Traversable
import Hyper.Class.Unify (UnifyGen)
import Hyper.Combinator.Compose (HComposeConstraint1)
import Hyper.Infer
import Hyper.Infer.Blame (Blame (..))
import Hyper.Unify.New (newUnbound)
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

type instance InferOf (HCompose Prune t) = InferOf t

instance
    ( Infer m t
    , HPointed (InferOf t)
    , HTraversable (InferOf t)
    , HNodesConstraint t (HComposeConstraint1 (Infer m) Prune)
    ) =>
    Infer m (HCompose Prune t)
    where
    inferBody (HCompose Pruned) =
        hpure (Proxy @(UnifyGen m) #> MkContainedH newUnbound)
            \\ inferContext (Proxy @m) (Proxy @t)
            & hsequence
            <&> (_HCompose # Pruned,)
    inferBody (HCompose (Unpruned (HCompose x))) =
        hmap
            ( \_ (HCompose (InferChild i)) ->
                i
                    <&> (\(InferredChild r t) -> InferredChild (_HCompose # r) t)
                    & InferChild
            )
            x
            & inferBody
            <&> Lens._1 %~ (hcomposed _Unpruned #)
    inferContext m _ = Dict \\ inferContext m (Proxy @t)

instance
    ( Blame m t
    , HNodesConstraint t (HComposeConstraint1 (Infer m) Prune)
    , HNodesConstraint t (HComposeConstraint1 (Blame m) Prune)
    , HNodesConstraint t (HComposeConstraint1 RNodes Prune)
    , HNodesConstraint t (HComposeConstraint1 (Recursively HFunctor) Prune)
    , HNodesConstraint t (HComposeConstraint1 (Recursively HFoldable) Prune)
    , HNodesConstraint t (HComposeConstraint1 RTraversable Prune)
    ) =>
    Blame m (HCompose Prune t)
    where
    inferOfUnify _ = inferOfUnify (Proxy @t)
    inferOfMatches _ = inferOfMatches (Proxy @t)
