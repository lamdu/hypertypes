{-# LANGUAGE UndecidableInstances, ScopedTypeVariables, TemplateHaskell, FlexibleInstances #-}

module Hyper.Type.Prune
    ( Prune(..)
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint (Dict(..), withDict)
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Hyper
import           Hyper.Class.Traversable
import           Hyper.Class.Unify (Unify)
import           Hyper.Infer
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Type.Combinator.Compose (Compose(..))
import           Hyper.Unify.New (newUnbound)

import           Prelude.Compat

data Prune h =
    Pruned | Unpruned (h # Prune)
    deriving Generic

makeCommonInstances [''Prune]
Lens.makePrisms ''Prune
makeHTraversableAndBases ''Prune
makeZipMatch ''Prune

-- `HPointed` and `HApplicative` instances in the spirit of `Maybe`

instance HPointed Prune where
    hpure f = Unpruned (f W_Prune_Prune)

instance HApply Prune where
    hzip Pruned _ = Pruned
    hzip _ Pruned = Pruned
    hzip (Unpruned x) (Unpruned y) = x :*: y & Unpruned

instance RNodes Prune
instance c Prune => Recursively c Prune
instance RTraversable Prune

type instance InferOf (Compose Prune t) = InferOf t

instance
    ( Infer m t
    , HPointed (InferOf t)
    , HTraversable (InferOf t)
    ) =>
    Infer m (Compose Prune t) where
    inferBody (MkCompose Pruned) =
        withDict (inferContext (Proxy @m) (Proxy @t)) $
        hpure (Proxy @(Unify m) #> MkContainedH newUnbound)
        & hsequence
        <&> (MkCompose Pruned, )
    inferBody (MkCompose (Unpruned (MkCompose x))) =
        hmap
        ( \_ (MkCompose (InferChild i)) ->
            i <&> (\(InferredChild r t) -> InferredChild (MkCompose r) t)
            & InferChild
        ) x
        & inferBody
        <&> Lens._1 %~ MkCompose . Unpruned . MkCompose
    inferContext m t = withDict (inferContext m t) Dict
