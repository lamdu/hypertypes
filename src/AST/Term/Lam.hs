{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, UndecidableInstances #-}
{-# LANGUAGE TupleSections, TypeFamilies, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module AST.Term.Lam
    ( Lam(..), lamIn, lamOut
    ) where

import           AST
import           AST.Class.Infer
import           AST.Term.FuncType
import           AST.Unify (UVar, newUnbound, newTerm)
import           Control.DeepSeq (NFData)
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint ((<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data Lam v expr k = Lam
    { _lamIn :: v
    , _lamOut :: Tie k expr
    } deriving Generic
makeLenses ''Lam

type Deps v expr k cls = ((cls v, cls (Tie k expr)) :: Constraint)

instance Deps v expr k Pretty => Pretty (Lam v expr k) where
    pPrintPrec lvl p (Lam i o) =
        (Pretty.text "λ" <> pPrintPrec lvl 0 i)
        <+> Pretty.text "->" <+> pPrintPrec lvl 0 o
        & maybeParens (p > 0)

makeChildren ''Lam
instance RecursiveConstraint (Lam v expr) constraint => Recursive constraint (Lam v expr)

type instance TypeOf  (Lam v t) = TypeOf  t
type instance ScopeOf (Lam v t) = ScopeOf t

instance
    ( Infer m t
    , HasFuncType (TypeOf t)
    , LocalScopeType v (Tree (UVar m) (TypeOf t)) m
    ) =>
    Infer m (Lam v t) where

    {-# INLINE infer #-}
    infer (Lam p r) =
        do
            varType <- newUnbound
            rI <- localScopeType p varType (inferNode r)
            funcType # FuncType
                { _funcIn = varType
                , _funcOut = rI ^. iType
                } & newTerm
                <&> (, Lam p rI)

deriving instance Deps v expr k Eq   => Eq   (Lam v expr k)
deriving instance Deps v expr k Ord  => Ord  (Lam v expr k)
deriving instance Deps v expr k Show => Show (Lam v expr k)
instance Deps v expr k Binary => Binary (Lam v expr k)
instance Deps v expr k NFData => NFData (Lam v expr k)
