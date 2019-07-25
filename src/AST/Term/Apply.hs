{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving, DeriveGeneric #-}

module AST.Term.Apply
    ( Apply(..), applyFunc, applyArg
    , applyChildren
    ) where

import AST
import AST.Combinator.Single (Single)
import AST.Infer
import AST.Term.FuncType
import AST.Unify (unify)
import AST.Unify.New (newTerm, newUnbound)
import Control.DeepSeq (NFData)
import Control.Lens (Traversal, makeLenses)
import Control.Lens.Operators
import Data.Binary (Binary)
import GHC.Generics (Generic)
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import Prelude.Compat

data Apply expr k = Apply
    { _applyFunc :: Node k expr
    , _applyArg :: Node k expr
    } deriving Generic

instance HasNodes (Apply e) where
    type NodeTypesOf (Apply e) = Single e

makeLenses ''Apply
makeZipMatch ''Apply
makeKApplicativeBases ''Apply
makeKTraversableAndFoldable ''Apply

instance Pretty (Node k expr) => Pretty (Apply expr k) where
    pPrintPrec lvl p (Apply f x) =
        pPrintPrec lvl 10 f <+>
        pPrintPrec lvl 11 x
        & maybeParens (p > 10)

instance RecursiveContext (Apply expr) constraint => Recursive constraint (Apply expr)

-- Type changing traversal.
-- TODO: Could the normal `Children` class support this?
applyChildren ::
    Traversal (Apply t0 f0) (Apply t1 f1) (Node f0 t0) (Node f1 t1)
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

deriving instance Eq   (Node k expr) => Eq   (Apply expr k)
deriving instance Ord  (Node k expr) => Ord  (Apply expr k)
deriving instance Show (Node k expr) => Show (Apply expr k)
instance Binary (Node k expr) => Binary (Apply expr k)
instance NFData (Node k expr) => NFData (Apply expr k)
