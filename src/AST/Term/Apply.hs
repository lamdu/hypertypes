{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TupleSections, StandaloneDeriving, DeriveGeneric, ScopedTypeVariables #-}

module AST.Term.Apply
    ( Apply(..), applyFunc, applyArg
    , applyChildren
    ) where

import           AST.Class.Infer (Infer(..), inferNode, nodeType, TypeAST, FuncType(..))
import           AST.Class.Recursive (Recursive(..), RecursiveConstraint)
import           AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import           AST.Knot (Tie)
import           AST.Unify (Unify(..), unify, newTerm, newUnbound)
import           Control.DeepSeq (NFData)
import           Control.Lens (Traversal)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Dict, withDict)
import           GHC.Generics (Generic)

import           Prelude.Compat

data Apply expr f = Apply
    { _applyFunc :: Tie f expr
    , _applyArg :: Tie f expr
    } deriving Generic

deriving instance Eq   (Tie f expr) => Eq   (Apply expr f)
deriving instance Ord  (Tie f expr) => Ord  (Apply expr f)
deriving instance Show (Tie f expr) => Show (Apply expr f)
instance (Binary (Tie f expr)) => Binary (Apply expr f)
instance (NFData (Tie f expr)) => NFData (Apply expr f)

Lens.makeLenses ''Apply
makeChildrenAndZipMatch [''Apply]

instance RecursiveConstraint (Apply expr) constraint => Recursive constraint (Apply expr)

-- Type changing traversal.
-- TODO: Could the normal `Children` class support this?
applyChildren ::
    Traversal (Apply t0 f0) (Apply t1 f1) (Tie f0 t0) (Tie f1 t1)
applyChildren f (Apply x0 x1) = Apply <$> f x0 <*> f x1

type instance TypeAST (Apply expr) = TypeAST expr

instance (Infer m expr, FuncType (TypeAST expr)) => Infer m (Apply expr) where
    infer (Apply func arg) =
        withDict (recursive :: Dict (RecursiveConstraint (TypeAST expr) (Unify m))) $
        do
            argI <- inferNode arg
            funcI <- inferNode func
            funcRes <- newUnbound
            funcT <- funcType # (argI ^. nodeType, funcRes) & newTerm
            funcRes <$ unify funcT (funcI ^. nodeType)
                <&> (, Apply funcI argI)
