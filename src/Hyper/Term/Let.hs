{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module Hyper.Term.Let
    ( Let(..), letVar, letEquals, letIn, KWitness(..)
    ) where

import           Hyper
import           Hyper.Class.Unify (Unify, UVarOf)
import           Hyper.Infer
import           Hyper.Unify.Generalize (GTerm, generalize)
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Proxy (Proxy(..))
import           Generics.Constraints (Constraints)
import           GHC.Generics (Generic)
import           Text.PrettyPrint (($+$), (<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A term for let-expressions with let-generalization.
--
-- @Let v expr@s express let-expressions with @v@s as variable names and @expr@s for terms.
--
-- Apart from the data type, an 'Infer' instance is also provided.
data Let v expr k = Let
    { _letVar :: v
    , _letEquals :: k # expr
    , _letIn :: k # expr
    } deriving (Generic)

makeLenses ''Let
makeCommonInstances [''Let]
makeKTraversableApplyAndBases ''Let
makeZipMatch ''Let

instance
    Constraints (Let v expr k) Pretty =>
    Pretty (Let v expr k) where
    pPrintPrec lvl p (Let v e i) =
        Pretty.text "let" <+> pPrintPrec lvl 0 v <+> Pretty.text "="
        <+> pPrintPrec lvl 0 e
        $+$ pPrintPrec lvl 0 i
        & maybeParens (p > 0)

type instance InferOf (Let v e) = InferOf e

instance
    ( MonadScopeLevel m
    , LocalScopeType v (Tree (GTerm (UVarOf m)) (TypeOf expr)) m
    , Unify m (TypeOf expr)
    , HasInferredType expr
    , KNodesConstraint (InferOf expr) (Unify m)
    , KTraversable (InferOf expr)
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
