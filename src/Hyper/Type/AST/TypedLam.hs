{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module Hyper.Type.AST.TypedLam
    ( TypedLam(..), tlIn, tlInType, tlOut
    ) where

import           Hyper
import           Hyper.Class.Has (HasChild(..))
import           Hyper.Infer
import           Hyper.Type.AST.FuncType (FuncType(..))
import           Hyper.Unify (Unify, UVarOf)
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Proxy (Proxy(..))
import           Generics.Constraints (Constraints)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data TypedLam var typ expr k = TypedLam
    { _tlIn :: var
    , _tlInType :: k # typ
    , _tlOut :: k # expr
    } deriving Generic

makeLenses ''TypedLam
makeCommonInstances [''TypedLam]
makeHTraversableApplyAndBases ''TypedLam
makeZipMatch ''TypedLam

instance
    Constraints (TypedLam var typ expr k) Pretty =>
    Pretty (TypedLam var typ expr k) where
    pPrintPrec lvl p (TypedLam i t o) =
        (Pretty.text "λ" <> pPrintPrec lvl 0 i
            <> Pretty.text ":" <> pPrintPrec lvl 0 t
        ) <+> Pretty.text "→" <+> pPrintPrec lvl 0 o
        & maybeParens (p > 0)

type instance InferOf (TypedLam v t e) = FuncType (TypeOf e)

instance
    ( Infer m t
    , Infer m e
    , HasInferredType e
    , Unify m (TypeOf e)
    , HasChild (InferOf t) (TypeOf e)
    , LocalScopeType v (Tree (UVarOf m) (TypeOf e)) m
    ) =>
    Infer m (TypedLam v t e) where

    {-# INLINE inferBody #-}
    inferBody (TypedLam p t r) =
        do
            InferredChild tI tR <- inferChild t
            let tT = tR ^. getChild
            InferredChild rI rR <- inferChild r & localScopeType p tT
            pure
                ( TypedLam p tI rI
                , FuncType tT (rR ^# inferredType (Proxy @e))
                )
