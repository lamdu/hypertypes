{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric, DataKinds #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances #-}

module AST.Term.Lam
    ( Lam(..), lamIn, lamOut
    ) where

import           AST
import           AST.Combinator.Single (Single)
import           AST.Infer
import           AST.Term.FuncType
import           AST.Unify (UVarOf)
import           AST.Unify.New (newTerm, newUnbound)
import           Control.DeepSeq (NFData)
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           Data.TyFun
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data Lam v expr k = Lam
    { _lamIn :: v
    , _lamOut :: Node k expr
    } deriving Generic
makeLenses ''Lam

instance KNodes (Lam v e) where
    type NodeTypesOf (Lam v e) = Single e
    type NodesConstraint (Lam v e) = On e

makeKTraversableAndBases ''Lam

type Deps v expr k cls = ((cls v, cls (Node k expr)) :: Constraint)

instance Deps v expr k Pretty => Pretty (Lam v expr k) where
    pPrintPrec lvl p (Lam i o) =
        (Pretty.text "λ" <> pPrintPrec lvl 0 i)
        <+> Pretty.text "->" <+> pPrintPrec lvl 0 o
        & maybeParens (p > 0)

instance RecursiveContext (Lam v expr) constraint => Recursively constraint (Lam v expr)

type instance TypeOf  (Lam v t) = TypeOf  t
type instance ScopeOf (Lam v t) = ScopeOf t
type instance ScopeOf (Lam v t) = ScopeOf t

instance
    ( Infer m t
    , HasFuncType (TypeOf t)
    , LocalScopeType v (Tree (UVarOf m) (TypeOf t)) m
    ) =>
    Infer m (Lam v t) where

    {-# INLINE inferBody #-}
    inferBody (Lam p r) =
        do
            varType <- newUnbound
            InferredChild rI rT <- inferChild r & localScopeType p varType
            funcType # FuncType varType rT & newTerm <&> InferRes (Lam p rI)

deriving instance Deps v expr k Eq   => Eq   (Lam v expr k)
deriving instance Deps v expr k Ord  => Ord  (Lam v expr k)
deriving instance Deps v expr k Show => Show (Lam v expr k)
instance Deps v expr k Binary => Binary (Lam v expr k)
instance Deps v expr k NFData => NFData (Lam v expr k)
