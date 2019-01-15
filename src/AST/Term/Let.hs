{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric, TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, UndecidableInstances #-}
{-# LANGUAGE TupleSections, FlexibleInstances, MultiParamTypeClasses #-}

module AST.Term.Let
    ( Let(..), letVar, letEquals, letIn
    ) where

import           AST
import           AST.Class.Infer
import           AST.Class.Infer.ScopeLevel (MonadScopeLevel(..))
import           AST.Class.Unify (UVar)
import           AST.Unify.Generalize (Generalized, generalize)
import           Control.DeepSeq (NFData)
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           GHC.Generics (Generic)
import           Text.PrettyPrint (($+$), (<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data Let v expr k = Let
    { _letVar :: v
    , _letEquals :: Tie k expr
    , _letIn :: Tie k expr
    } deriving (Generic)
makeLenses ''Let

type Deps v expr k cls = ((cls v, cls (Tie k expr)) :: Constraint)

instance Deps v expr k Pretty => Pretty (Let v expr k) where
    pPrintPrec lvl p (Let v e i) =
        Pretty.text "let" <+> pPrintPrec lvl 0 v <+> Pretty.text "="
        <+> pPrintPrec lvl 0 e
        $+$ pPrintPrec lvl 0 i
        & maybeParens (p > 0)

makeChildren ''Let
instance RecursiveConstraint (Let v expr) constraint => Recursive constraint (Let v expr)

type instance TypeOf  (Let v t) = TypeOf  t
type instance ScopeOf (Let v t) = ScopeOf t

instance
    ( MonadScopeLevel m
    , Infer m expr
    , LocalScopeType v (Tree (Generalized (TypeOf expr)) (UVar m)) m
    ) =>
    Infer m (Let v expr) where

    infer (Let v e i) =
        do
            (eI, eG) <-
                do
                    eI <- inferNode e
                    generalize (eI ^. iType) <&> (eI ,)
                & localLevel
            iI <- localScopeType v eG (inferNode i)
            pure (iI ^. iType, Let v eI iI)

deriving instance Deps v expr k Eq   => Eq   (Let v expr k)
deriving instance Deps v expr k Ord  => Ord  (Let v expr k)
deriving instance Deps v expr k Show => Show (Let v expr k)
instance Deps v expr k Binary => Binary (Let v expr k)
instance Deps v expr k NFData => NFData (Let v expr k)
