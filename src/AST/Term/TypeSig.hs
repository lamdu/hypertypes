{-# LANGUAGE UndecidableInstances, TemplateHaskell, FlexibleInstances #-}

module AST.Term.TypeSig
    ( TypeSig(..), tsType, tsTerm
    ) where

import           AST
import           AST.Combinator.Flip (_Flip)
import           AST.Infer
import           AST.Term.Scheme
import           AST.Unify (Unify, unify)
import           AST.Unify.Generalize (instantiateWith)
import           AST.Unify.Term (UTerm(..))
import           Control.DeepSeq (NFData)
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Proxy (Proxy(..))
import           Generics.OneLiner (Constraints)
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data TypeSig vars term k = TypeSig
    { _tsTerm :: Node k term
    , _tsType :: Node k (Scheme vars (TypeOf term))
    } deriving Generic
makeLenses ''TypeSig

makeKTraversableApplyAndBases ''TypeSig

instance
    Constraints (TypeSig vars term k) Pretty =>
    Pretty (TypeSig vars term k) where
    pPrintPrec lvl p (TypeSig term typ) =
        pPrintPrec lvl 1 term <+> Pretty.text ":" <+> pPrintPrec lvl 1 typ
        & maybeParens (p > 1)

instance
    ( Inferrable t
    , KTraversable (InferOf t)
    , Inferrable (TypeOf t)
    , RTraversable (TypeOf t)
    ) =>
    Inferrable (TypeSig v t) where
    type InferOf (TypeSig v t) = InferOf t

instance
    ( MonadScopeLevel m
    , HasInferredType term
    , HasInferredValue (TypeOf term)
    , KTraversable vars
    , KTraversable (InferOf term)
    , NodesConstraint (InferOf term) (Unify m)
    , NodesConstraint vars (MonadInstantiate m)
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
                <&> InferRes (TypeSig xI sI)
        & localLevel

deriving instance Constraints (TypeSig v t k) Eq   => Eq   (TypeSig v t k)
deriving instance Constraints (TypeSig v t k) Ord  => Ord  (TypeSig v t k)
deriving instance Constraints (TypeSig v t k) Show => Show (TypeSig v t k)
instance Constraints (TypeSig v t k) Binary => Binary (TypeSig v t k)
instance Constraints (TypeSig v t k) NFData => NFData (TypeSig v t k)
