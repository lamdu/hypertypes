{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module Hyper.Type.AST.Let
    ( Let(..), letVar, letEquals, letIn, W_Let(..), MorphWitness(..)
    ) where

import           Generics.Constraints (Constraints)
import           Hyper
import           Hyper.Class.Morph (HMorph(..))
import           Hyper.Class.Unify (UnifyGen, UVarOf)
import           Hyper.Infer
import           Hyper.Unify.Generalize (GTerm, generalize)
import           Text.PrettyPrint (($+$), (<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Hyper.Internal.Prelude

-- | A term for let-expressions with let-generalization.
--
-- @Let v expr@s express let-expressions with @v@s as variable names and @expr@s for terms.
--
-- Apart from the data type, an 'Infer' instance is also provided.
data Let v expr h = Let
    { _letVar :: v
    , _letEquals :: h :# expr
    , _letIn :: h :# expr
    } deriving (Generic)

makeLenses ''Let
makeCommonInstances [''Let]
makeHTraversableApplyAndBases ''Let
makeZipMatch ''Let
makeHContext ''Let

instance HMorph (Let v a) (Let v b) where
    type instance MorphConstraint (Let v a) (Let v b) c = c a b
    data instance MorphWitness _ _ _ _ where
        M_Let :: MorphWitness (Let v a) (Let v b) a b
    morphMap f (Let v x y) = Let v (f M_Let x) (f M_Let y)
    morphLiftConstraint M_Let _ = id

instance
    Constraints (Let v expr h) Pretty =>
    Pretty (Let v expr h) where
    pPrintPrec lvl p (Let v e i) =
        Pretty.text "let" <+> pPrintPrec lvl 0 v <+> Pretty.text "="
        <+> pPrintPrec lvl 0 e
        $+$ pPrintPrec lvl 0 i
        & maybeParens (p > 0)

type instance InferOf (Let _ e) = InferOf e

instance
    ( MonadScopeLevel m
    , LocalScopeType v (GTerm (UVarOf m) # TypeOf expr) m
    , UnifyGen m (TypeOf expr)
    , HasInferredType expr
    , HNodesConstraint (InferOf expr) (UnifyGen m)
    , HTraversable (InferOf expr)
    , Infer m expr
    ) =>
    Infer m (Let v expr) where

    inferBody (Let v e i) =
        do
            (eI, eG) <-
                do
                    InferredChild eI eR <- inferChild e
                    generalize (eR ^# inferredType (Proxy @expr))
                        <&> (eI ,)
                & localLevel
            inferChild i
                & localScopeType v eG
                <&> \(InferredChild iI iR) -> (Let v eI iI, iR)
