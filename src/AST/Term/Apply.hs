{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TupleSections, StandaloneDeriving, DeriveGeneric, ScopedTypeVariables #-}

module AST.Term.Apply
    ( Apply(..), applyFunc, applyArg
    , applyChildren
    ) where

import AST.Class.Infer (Infer(..), newUnbound, newTerm, inferNode, nodeType, TypeAST)
import AST.Class.Recursive (Recursive(..), RecursiveConstraint, RecursiveDict)
import AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import AST.Knot (Tie)
import AST.Term.FuncType
import AST.Unify (Unify(..), unify)
import Control.DeepSeq (NFData)
import Control.Lens (Traversal, makeLenses)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Constraint (withDict)
import GHC.Generics (Generic)

import Prelude.Compat

data Apply expr f = Apply
    { _applyFunc :: Tie f expr
    , _applyArg :: Tie f expr
    } deriving Generic

deriving instance Eq   (Tie f expr) => Eq   (Apply expr f)
deriving instance Ord  (Tie f expr) => Ord  (Apply expr f)
deriving instance Show (Tie f expr) => Show (Apply expr f)
instance Binary (Tie f expr) => Binary (Apply expr f)
instance NFData (Tie f expr) => NFData (Apply expr f)

makeLenses ''Apply
makeChildrenAndZipMatch [''Apply]

instance RecursiveConstraint (Apply expr) constraint => Recursive constraint (Apply expr)

-- Type changing traversal.
-- TODO: Could the normal `Children` class support this?
applyChildren ::
    Traversal (Apply t0 f0) (Apply t1 f1) (Tie f0 t0) (Tie f1 t1)
applyChildren f (Apply x0 x1) = Apply <$> f x0 <*> f x1

type instance TypeAST (Apply expr) = TypeAST expr

instance (Infer m expr, HasFuncType (TypeAST expr)) => Infer m (Apply expr) where
    infer (Apply func arg) =
        withDict (recursive :: RecursiveDict (Unify m) (TypeAST expr)) $
        do
            argI <- inferNode arg
            funcI <- inferNode func
            funcRes <- newUnbound
            funcT <-
                funcType # FuncType
                { _funcIn = argI ^. nodeType
                , _funcOut = funcRes
                } & newTerm
            funcRes <$ unify funcT (funcI ^. nodeType)
                <&> (, Apply funcI argI)
