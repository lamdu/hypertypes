{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances #-}

module AST.Term.Lam
    ( Lam(..), lamIn, lamOut, KWitness(..)
    ) where

import           AST
import           AST.Infer
import           AST.Term.FuncType
import           AST.Unify (Unify, UVarOf)
import           AST.Unify.New (newUnbound)
import           AST.TH.Internal.Instances (makeCommonInstances)
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Proxy (Proxy(..))
import           Generics.Constraints (Constraints)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A term for lambda abstractions.
--
-- @Lam v expr@s express lambda abstractions with @v@s as variable names and @expr@s for bodies.
--
-- Apart from the data type, an 'Infer' instance is also provided.
data Lam v expr k = Lam
    { _lamIn :: v
    , _lamOut :: k # expr
    } deriving Generic

makeLenses ''Lam
makeCommonInstances [''Lam]
makeKTraversableApplyAndBases ''Lam

instance
    Constraints (Lam v expr k) Pretty =>
    Pretty (Lam v expr k) where
    pPrintPrec lvl p (Lam i o) =
        (Pretty.text "λ" <> pPrintPrec lvl 0 i)
        <+> Pretty.text "→" <+> pPrintPrec lvl 0 o
        & maybeParens (p > 0)

type instance InferOf (Lam v t) = FuncType (TypeOf t)

instance
    ( Infer m t
    , Unify m (TypeOf t)
    , HasInferredType t
    , LocalScopeType v (Tree (UVarOf m) (TypeOf t)) m
    ) =>
    Infer m (Lam v t) where

    {-# INLINE inferBody #-}
    inferBody (Lam p r) =
        do
            varType <- newUnbound
            inferChild r & localScopeType p varType
                <&>
                \(InferredChild rI rR) ->
                ( Lam p rI
                , FuncType varType (rR ^# inferredType (Proxy @t))
                )
