{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric, StandaloneDeriving, KindSignatures, ConstraintKinds, UndecidableInstances, TupleSections, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}

module AST.Term.Lam
    ( Lam(..), lamIn, lamOut
    , ScopeTypes, HasScopeTypes(..)
    ) where

import           AST.Class.Children.TH (makeChildren)
import           AST.Class.Infer (Infer(..), TypeAST, newUnbound, newTerm, inferNode, nodeType)
import           AST.Class.Recursive (Recursive(..), RecursiveConstraint, RecursiveDict)
import           AST.Knot (Tie, Tree)
import           AST.Term.FuncType
import           AST.Unify (Unify(..), UniVar)
import           Control.DeepSeq (NFData)
import           Control.Lens (Lens')
import           Control.Lens.Operators
import qualified Control.Lens as Lens
import           Control.Monad.Reader (MonadReader, local)
import           Data.Binary (Binary)
import           Data.Constraint (Constraint, withDict)
import           Data.Map (Map)
import           GHC.Generics (Generic)

import           Prelude.Compat

data Lam v expr f = Lam
    { _lamIn :: v
    , _lamOut :: Tie f expr
    } deriving Generic
Lens.makeLenses ''Lam

type Deps v expr f cls = ((cls v, cls (Tie f expr)) :: Constraint)
-- Note that `Eq` is not alpha-equivalence!
deriving instance Deps v expr f Eq   => Eq   (Lam v expr f)
deriving instance Deps v expr f Ord  => Ord  (Lam v expr f)
deriving instance Deps v expr f Show => Show (Lam v expr f)
instance Deps v expr f Binary => Binary (Lam v expr f)
instance Deps v expr f NFData => NFData (Lam v expr f)

makeChildren ''Lam
instance RecursiveConstraint (Lam v expr) constraint => Recursive constraint (Lam v expr)

type ScopeTypes v u t = Map v (Tree u t)

class Ord v => HasScopeTypes v u t env where
    scopeTypes :: Lens' env (ScopeTypes v u t)

instance Ord v => HasScopeTypes v u t (ScopeTypes v u t) where
    scopeTypes = id

type instance TypeAST (Lam v t) = TypeAST t

instance
    ( Infer m t
    , HasFuncType (TypeAST t)
    , MonadReader env m
    , HasScopeTypes v (UniVar m) (TypeAST t) env
    ) =>
    Infer m (Lam v t) where

    infer (Lam p r) =
        withDict (recursive :: RecursiveDict (Unify m) (TypeAST t)) $
        do
            varType <- newUnbound
            rI <-
                local
                (scopeTypes . Lens.at p ?~ varType)
                (inferNode r)
            funcType # FuncType
                { _funcIn = varType
                , _funcOut = rI ^. nodeType
                } & newTerm
                <&> (, Lam p rI)
