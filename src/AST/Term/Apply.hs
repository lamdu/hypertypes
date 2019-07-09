{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving, DeriveGeneric #-}

module AST.Term.Apply
    ( Apply(..), applyFunc, applyArg
    , applyChildren
    ) where

import AST
import AST.Infer
import AST.Term.FuncType
import AST.Unify (unify, newUnbound, newTerm)
import Control.DeepSeq (NFData)
import Control.Lens (Traversal, makeLenses)
import Control.Lens.Operators
import Data.Binary (Binary)
import GHC.Generics (Generic)
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import Prelude.Compat

data Apply expr k = Apply
    { _applyFunc :: Tie k expr
    , _applyArg :: Tie k expr
    } deriving Generic

instance Pretty (Tie k expr) => Pretty (Apply expr k) where
    pPrintPrec lvl p (Apply f x) =
        pPrintPrec lvl 10 f <+>
        pPrintPrec lvl 11 x
        & maybeParens (p > 10)

makeLenses ''Apply
makeChildrenAndZipMatch ''Apply

instance RecursiveConstraint (Apply expr) constraint => Recursive constraint (Apply expr)

-- Type changing traversal.
-- TODO: Could the normal `Children` class support this?
applyChildren ::
    Traversal (Apply t0 f0) (Apply t1 f1) (Tie f0 t0) (Tie f1 t1)
applyChildren f (Apply x0 x1) = Apply <$> f x0 <*> f x1

type instance TypeOf  (Apply expr) = TypeOf  expr
type instance ScopeOf (Apply expr) = ScopeOf expr

instance (Infer m expr, HasFuncType (TypeOf expr)) => Infer m (Apply expr) where
    {-# INLINE inferBody #-}
    inferBody (Apply func arg) =
        do
            InferredChild argI argT <- inferChild arg
            InferredChild funcI funcT <- inferChild func
            funcRes <- newUnbound
            InferRes (Apply funcI argI) funcRes <$
                (newTerm (funcType # FuncType argT funcRes) >>= unify funcT)

deriving instance Eq   (Tie k expr) => Eq   (Apply expr k)
deriving instance Ord  (Tie k expr) => Ord  (Apply expr k)
deriving instance Show (Tie k expr) => Show (Apply expr k)
instance Binary (Tie k expr) => Binary (Apply expr k)
instance NFData (Tie k expr) => NFData (Apply expr k)
