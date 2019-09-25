-- | Type signatures

{-# LANGUAGE UndecidableInstances, TemplateHaskell, FlexibleInstances #-}

module Hyper.Type.AST.TypeSig
    ( TypeSig(..), tsType, tsTerm, KWitness(..)
    ) where

import           Hyper
import           Hyper.Combinator.Flip (_Flip)
import           Hyper.Infer
import           Hyper.Type.AST.Scheme
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Unify (Unify, unify)
import           Hyper.Unify.Generalize (instantiateWith)
import           Hyper.Unify.Term (UTerm(..))
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Proxy (Proxy(..))
import           Generics.Constraints (Constraints)
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data TypeSig vars term k = TypeSig
    { _tsTerm :: k # term
    , _tsType :: k # Scheme vars (TypeOf term)
    } deriving Generic

makeLenses ''TypeSig
makeCommonInstances [''TypeSig]
makeKTraversableApplyAndBases ''TypeSig

instance
    Constraints (TypeSig vars term k) Pretty =>
    Pretty (TypeSig vars term k) where
    pPrintPrec lvl p (TypeSig term typ) =
        pPrintPrec lvl 1 term <+> Pretty.text ":" <+> pPrintPrec lvl 1 typ
        & maybeParens (p > 1)

type instance InferOf (TypeSig v t) = InferOf t

instance
    ( MonadScopeLevel m
    , HasInferredType term
    , HasInferredValue (TypeOf term)
    , KTraversable vars
    , KTraversable (InferOf term)
    , KNodesConstraint (InferOf term) (Unify m)
    , KNodesConstraint vars (MonadInstantiate m)
    , Unify m (TypeOf term)
    , Infer m (TypeOf term)
    , Infer m term
    ) =>
    Infer m (TypeSig vars term) where

    inferBody (TypeSig x s) =
        do
            InferredChild xI xR <- inferChild x
            InferredChild sI sR <- inferChild s
            (t, ()) <- instantiateWith (pure ()) USkolem (sR ^. _Flip)
            xR & inferredType (Proxy @term) #%%~ unify t
                <&> (TypeSig xI sI, )
        & localLevel
