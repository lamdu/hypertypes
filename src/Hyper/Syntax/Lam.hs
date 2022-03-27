{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances, FlexibleContexts #-}

module Hyper.Syntax.Lam
    ( Lam(..), lamIn, lamOut, W_Lam(..), MorphWitness(..)
    ) where

import           Generics.Constraints (Constraints)
import           Hyper
import           Hyper.Class.Optic (HSubset(..), HSubset')
import           Hyper.Infer
import           Hyper.Syntax.FuncType
import           Hyper.Unify (UnifyGen, UVarOf)
import           Hyper.Unify.New (newUnbound, newTerm)
import qualified Text.PrettyPrint as P
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Hyper.Internal.Prelude

-- | A term for lambda abstractions.
--
-- @Lam v expr@s express lambda abstractions with @v@s as variable names and @expr@s for bodies.
--
-- Apart from the data type, an 'Infer' instance is also provided.
data Lam v expr h = Lam
    { _lamIn :: v
    , _lamOut :: h :# expr
    } deriving Generic

makeLenses ''Lam
makeCommonInstances [''Lam]
makeHTraversableApplyAndBases ''Lam
makeZipMatch ''Lam
makeHContext ''Lam
makeHMorph ''Lam

instance RNodes t => RNodes (Lam v t)
instance (c (Lam v t), Recursively c t) => Recursively c (Lam v t)
instance RTraversable t => RTraversable (Lam v t)

instance
    Constraints (Lam v expr h) Pretty =>
    Pretty (Lam v expr h) where
    pPrintPrec lvl p (Lam i o) =
        (P.text "λ" <> pPrintPrec lvl 0 i)
        P.<+> P.text "→" P.<+> pPrintPrec lvl 0 o
        & maybeParens (p > 0)

type instance InferOf (Lam _ t) = ANode (TypeOf t)

instance
    ( Infer m t
    , UnifyGen m (TypeOf t)
    , HSubset' (TypeOf t) (FuncType (TypeOf t))
    , HasInferredType t
    , LocalScopeType v (UVarOf m # TypeOf t) m
    ) =>
    Infer m (Lam v t) where

    {-# INLINE inferBody #-}
    inferBody (Lam p r) =
        do
            varType <- newUnbound
            InferredChild rI rR <- inferChild r & localScopeType p varType
            hSubset # FuncType varType (rR ^# inferredType (Proxy @t))
                & newTerm
                <&> MkANode
                <&> (Lam p rI,)
