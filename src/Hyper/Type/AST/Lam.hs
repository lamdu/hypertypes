{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances #-}

module Hyper.Type.AST.Lam
    ( Lam(..), lamIn, lamOut, W_Lam(..)
    ) where

import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Generics.Constraints (Constraints)
import           Hyper
import           Hyper.Infer
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Type.AST.FuncType
import           Hyper.Unify (Unify, UVarOf)
import           Hyper.Unify.New (newUnbound, newTerm)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A term for lambda abstractions.
--
-- @Lam v expr@s express lambda abstractions with @v@s as variable names and @expr@s for bodies.
--
-- Apart from the data type, an 'Infer' instance is also provided.
data Lam v expr h = Lam
    { _lamIn :: v
    , _lamOut :: h # expr
    } deriving Generic

makeLenses ''Lam
makeCommonInstances [''Lam]
makeHTraversableApplyAndBases ''Lam
makeZipMatch ''Lam

instance RNodes t => RNodes (Lam v t)
instance (c (Lam v t), Recursively c t) => Recursively c (Lam v t)
instance RTraversable t => RTraversable (Lam v t)

instance
    Constraints (Lam v expr h) Pretty =>
    Pretty (Lam v expr h) where
    pPrintPrec lvl p (Lam i o) =
        (Pretty.text "λ" <> pPrintPrec lvl 0 i)
        <+> Pretty.text "→" <+> pPrintPrec lvl 0 o
        & maybeParens (p > 0)

type instance InferOf (Lam v t) = ANode (TypeOf t)

instance
    ( Infer m t
    , Unify m (TypeOf t)
    , HasFuncType (TypeOf t)
    , HasInferredType t
    , LocalScopeType v (Tree (UVarOf m) (TypeOf t)) m
    ) =>
    Infer m (Lam v t) where

    {-# INLINE inferBody #-}
    inferBody (Lam p r) =
        do
            varType <- newUnbound
            InferredChild rI rR <- inferChild r & localScopeType p varType
            funcType # FuncType varType (rR ^# inferredType (Proxy @t))
                & newTerm
                <&> MkANode
                <&> (Lam p rI,)
