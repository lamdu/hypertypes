{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric, StandaloneDeriving, ConstraintKinds, UndecidableInstances, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}

module AST.Term.Let
    ( Let(..), letVar, letEquals, letIn
    ) where

import AST.Class.Children.TH (makeChildren)
import AST.Class.Infer
import AST.Class.Instantiate
import AST.Class.Recursive (Recursive(..), RecursiveConstraint)
import AST.Knot (Tie)
import AST.Term.Var
import AST.Unify (MonadUnify(..))
import AST.Unify.Generalize
import Control.DeepSeq (NFData)
import Control.Lens (makeLenses)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Constraint (Constraint)
import GHC.Generics (Generic)

import Prelude.Compat

data Let v expr k = Let
    { _letVar :: v
    , _letEquals :: Tie k expr
    , _letIn :: Tie k expr
    } deriving (Generic)
makeLenses ''Let

type Deps v expr k cls = ((cls v, cls (Tie k expr)) :: Constraint)
-- Note that `Eq` is not alpha-equivalence!
deriving instance Deps v expr f Eq   => Eq   (Let v expr f)
deriving instance Deps v expr f Ord  => Ord  (Let v expr f)
deriving instance Deps v expr f Show => Show (Let v expr f)
instance Deps v expr f Binary => Binary (Let v expr f)
instance Deps v expr f NFData => NFData (Let v expr f)

makeChildren ''Let
instance RecursiveConstraint (Let v expr) constraint => Recursive constraint (Let v expr)

type instance TypeAST (Let v t) = TypeAST t

instance (Infer m expr, MonadScopeTypes v (TypeAST expr) m) => Infer m (Let v expr) where
    infer (Let v e i) =
        do
            (eI, innerScope) <- (,) <$> inferNode e <*> scopeConstraints & localLevel
            eG <- generalize innerScope (eI ^. nodeType)
            iI <- localScopeType v (instantiate eG) (inferNode i)
            pure (iI ^. nodeType, Let v eI iI)
