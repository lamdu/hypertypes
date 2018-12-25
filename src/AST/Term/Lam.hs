{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric, StandaloneDeriving, ConstraintKinds, UndecidableInstances, TupleSections, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}

module AST.Term.Lam
    ( Lam(..), lamIn, lamOut
    ) where

import AST.Class.Children.TH (makeChildren)
import AST.Class.Infer (Infer(..), TypeAST, newUnbound, newTerm, inferNode, nodeType)
import AST.Class.Recursive (Recursive(..), RecursiveConstraint, RecursiveDict)
import AST.Knot (Tie)
import AST.Term.FuncType
import AST.Term.Var
import AST.Unify (Unify(..))
import Control.DeepSeq (NFData)
import Control.Lens (makeLenses)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Constraint (Constraint, withDict)
import GHC.Generics (Generic)

import Prelude.Compat

data Lam v expr f = Lam
    { _lamIn :: v
    , _lamOut :: Tie f expr
    } deriving Generic
makeLenses ''Lam

type Deps v expr f cls = ((cls v, cls (Tie f expr)) :: Constraint)
-- Note that `Eq` is not alpha-equivalence!
deriving instance Deps v expr f Eq   => Eq   (Lam v expr f)
deriving instance Deps v expr f Ord  => Ord  (Lam v expr f)
deriving instance Deps v expr f Show => Show (Lam v expr f)
instance Deps v expr f Binary => Binary (Lam v expr f)
instance Deps v expr f NFData => NFData (Lam v expr f)

makeChildren ''Lam
instance RecursiveConstraint (Lam v expr) constraint => Recursive constraint (Lam v expr)

type instance TypeAST (Lam v t) = TypeAST t

instance
    ( Infer m t
    , HasFuncType (TypeAST t)
    , MonadScopeTypes v (TypeAST t) m
    ) =>
    Infer m (Lam v t) where

    infer (Lam p r) =
        withDict (recursive :: RecursiveDict (Unify m) (TypeAST t)) $
        do
            varType <- newUnbound
            rI <- localScopeType p (pure varType) (inferNode r)
            funcType # FuncType
                { _funcIn = varType
                , _funcOut = rI ^. nodeType
                } & newTerm
                <&> (, Lam p rI)
