{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances, FlexibleContexts #-}

module Hyper.Syntax.TypedLam
    ( TypedLam(..), tlIn, tlInType, tlOut, W_TypedLam(..), MorphWitness(..)
    ) where

import           Generics.Constraints (Constraints)
import           Hyper
import           Hyper.Class.Optic (HNodeLens(..), HSubset(..), HSubset')
import           Hyper.Infer
import           Hyper.Syntax.FuncType (FuncType(..))
import           Hyper.Unify (UnifyGen, UVarOf)
import           Hyper.Unify.New (newTerm)
import qualified Text.PrettyPrint as P
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Hyper.Internal.Prelude

data TypedLam var typ expr h = TypedLam
    { _tlIn :: var
    , _tlInType :: h :# typ
    , _tlOut :: h :# expr
    } deriving Generic

makeLenses ''TypedLam
makeCommonInstances [''TypedLam]
makeHTraversableApplyAndBases ''TypedLam
makeZipMatch ''TypedLam
makeHContext ''TypedLam
makeHMorph ''TypedLam

instance (RNodes t, RNodes e) => RNodes (TypedLam v t e)
instance
    (c (TypedLam v t e), Recursively c t, Recursively c e) =>
    Recursively c (TypedLam v t e)
instance (RTraversable t, RTraversable e) => RTraversable (TypedLam v t e)

instance
    Constraints (TypedLam var typ expr h) Pretty =>
    Pretty (TypedLam var typ expr h) where
    pPrintPrec lvl p (TypedLam i t o) =
        ( P.text "λ" <> pPrintPrec lvl 0 i
            <> P.text ":" <> pPrintPrec lvl 0 t
        ) P.<+> P.text "→" P.<+> pPrintPrec lvl 0 o
        & maybeParens (p > 0)

type instance InferOf (TypedLam _ _ e) = ANode (TypeOf e)

instance
    ( Infer m t
    , Infer m e
    , HasInferredType e
    , UnifyGen m (TypeOf e)
    , HSubset' (TypeOf e) (FuncType (TypeOf e))
    , HNodeLens (InferOf t) (TypeOf e)
    , LocalScopeType v (UVarOf m # TypeOf e) m
    ) =>
    Infer m (TypedLam v t e) where

    {-# INLINE inferBody #-}
    inferBody (TypedLam p t r) =
        do
            InferredChild tI tR <- inferChild t
            let tT = tR ^. hNodeLens
            InferredChild rI rR <- inferChild r & localScopeType p tT
            hSubset # FuncType tT (rR ^# inferredType (Proxy @e))
                & newTerm
                <&> MkANode
                <&> (TypedLam p tI rI,)
