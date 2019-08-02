{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, UndecidableInstances, FlexibleInstances #-}

module AST.Term.Let
    ( Let(..), letVar, letEquals, letIn
    ) where

import           AST
import           AST.Class.Unify (Unify, UVarOf)
import           AST.Combinator.ANode (ANode)
import           AST.Infer
import           AST.Unify.Generalize (GTerm, generalize)
import           Control.DeepSeq (NFData)
import           Control.Lens (makeLenses, cloneLens)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Text.PrettyPrint (($+$), (<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data Let v expr k = Let
    { _letVar :: v
    , _letEquals :: Node k expr
    , _letIn :: Node k expr
    } deriving (Generic)
makeLenses ''Let

instance KNodes (Let v e) where
    type NodeTypesOf (Let v e) = ANode e

makeKTraversableAndBases ''Let

type Deps v expr k cls = ((cls v, cls (Node k expr)) :: Constraint)

instance Deps v expr k Pretty => Pretty (Let v expr k) where
    pPrintPrec lvl p (Let v e i) =
        Pretty.text "let" <+> pPrintPrec lvl 0 v <+> Pretty.text "="
        <+> pPrintPrec lvl 0 e
        $+$ pPrintPrec lvl 0 i
        & maybeParens (p > 0)

instance RecursiveContext (Let v expr) constraint => Recursively constraint (Let v expr)

type instance InferOf (Let v expr) = InferOf expr

instance
    ( MonadScopeLevel m
    , LocalScopeType v (Tree (GTerm (UVarOf m)) (TypeOf expr)) m
    , Recursively (Unify m) (TypeOf expr)
    , HasInferredType expr
    ) =>
    Infer m (Let v expr) where

    inferBody (Let v e i) =
        do
            (eI, eG) <-
                do
                    InferredChild eI eR <- inferChild e
                    generalize (eR ^. cloneLens (inferredType (Proxy @expr)))
                        <&> (eI ,)
                & localLevel
            inferChild i
                & localScopeType v eG
                <&> \(InferredChild iI iR) -> InferRes (Let v eI iI) iR

deriving instance Deps v expr k Eq   => Eq   (Let v expr k)
deriving instance Deps v expr k Ord  => Ord  (Let v expr k)
deriving instance Deps v expr k Show => Show (Let v expr k)
instance Deps v expr k Binary => Binary (Let v expr k)
instance Deps v expr k NFData => NFData (Let v expr k)
