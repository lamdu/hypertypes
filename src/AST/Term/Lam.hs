{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DeriveGeneric, StandaloneDeriving, UndecidableInstances, GeneralizedNewtypeDeriving, TupleSections, MultiParamTypeClasses, TypeFamilies, FlexibleInstances, ScopedTypeVariables #-}

module AST.Term.Lam
    ( Lam(..), lamIn, lamOut
    , LamVar(..), _LamVar
    , ScopeTypes, HasScopeTypes(..)
    ) where

import           AST.Class.Infer
import           AST.Class.Recursive (Recursive(..), RecursiveConstraint)
import           AST.Class.TH (makeChildren)
import           AST.Functor.UTerm (UTerm(..), newUTerm)
import           AST.Node (Node)
import           AST.Unify
import           Control.DeepSeq (NFData)
import           Control.Lens (Lens')
import           Control.Lens.Operators
import qualified Control.Lens as Lens
import           Control.Monad.Reader (MonadReader, local)
import           Data.Binary (Binary)
import           Data.Constraint
import           Data.Map
import           Data.Maybe (fromMaybe)
import           GHC.Generics (Generic)

import           Prelude.Compat

data Lam v expr f = Lam
    { _lamIn :: v
    , _lamOut :: Node f expr
    } deriving Generic
Lens.makeLenses ''Lam

-- Note that `Eq` is not alpha-equivalence!
deriving instance (Eq   v, Eq   (Node f expr)) => Eq   (Lam v expr f)
deriving instance (Ord  v, Ord  (Node f expr)) => Ord  (Lam v expr f)
deriving instance (Show v, Show (Node f expr)) => Show (Lam v expr f)
instance (Binary v, Binary (Node f expr)) => Binary (Lam v expr f)
instance (NFData v, NFData (Node f expr)) => NFData (Lam v expr f)

newtype LamVar v (expr :: (* -> *) -> *) (f :: * -> *) = LamVar v
    deriving (Eq, Ord, Show, Generic, Binary, NFData)
Lens.makePrisms ''LamVar

makeChildren [''Lam, ''LamVar]
instance RecursiveConstraint (Lam v expr) constraint => Recursive constraint (Lam v expr)

type ScopeTypes v u t = Map v (Node (UTerm u) t)

class Ord v => HasScopeTypes v u t env where
    scopeTypes :: Lens' env (ScopeTypes v u t)

instance Ord v => HasScopeTypes v u t (ScopeTypes v u t) where
    scopeTypes = id

type instance TypeAST (Lam v t) = TypeAST t
type instance TypeAST (LamVar v t) = TypeAST t

instance
    ( Infer m t
    , FuncType (TypeAST t)
    , MonadReader env m
    , HasScopeTypes v (UniVar m) (TypeAST t) env
    ) =>
    Infer m (Lam v t) where

    infer (Lam p r) =
        withDict (recursive :: Dict (RecursiveConstraint (TypeAST t) (Unify m))) $
        do
            varType <- newVar binding
            rI <-
                local
                (scopeTypes . Lens.at p ?~ varType)
                (inferNode r)
            pure
                ( funcType # (varType, rI ^. nodeType) & newUTerm
                , Lam p rI
                )

instance
    ( Infer m t
    , MonadReader env m
    , HasScopeTypes v (UniVar m) (TypeAST t) env
    ) =>
    Infer m (LamVar v t) where

    infer (LamVar x) =
        Lens.view (scopeTypes . Lens.at x)
        <&> fromMaybe (error "name error")
        <&> (, LamVar x)
