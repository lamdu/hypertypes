{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, TemplateHaskell, KindSignatures, TypeFamilies, LambdaCase, EmptyCase, ScopedTypeVariables, TypeOperators, FlexibleInstances, MultiParamTypeClasses #-}

module AST.Scope
    ( Scope(..), ScopeVar(..), EmptyScope
    , DeBruijnIndex(..)
    , ScopeTypes, HasScopeTypes(..)
    ) where

import           AST (Node)
import           AST.Infer (InferMonad(..), InferMonad1(..), TypeAST, HasTypeAST1(..), sameTypeAst, FuncType(..))
import           AST.Recursive (ChildrenRecursive)
import           AST.Unify (UnifyMonad(..), Binding(..), Var)
import           AST.UTerm (UTerm(..))
import           AST.TH (makeChildrenAndZipMatch)
import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader (MonadReader, local)
import           Data.Constraint
import           Data.Functor.Identity (Identity(..))
import           Data.IntMap (IntMap)
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

data EmptyScope

newtype Scope expr a f = Scope (Node f (expr (Maybe a)))
newtype ScopeVar (expr :: * -> (* -> *) -> *) a (f :: * -> *) = ScopeVar a

makeChildrenAndZipMatch [''Scope, ''ScopeVar]
instance ChildrenRecursive (expr (Maybe a)) => ChildrenRecursive (Scope expr a)

class DeBruijnIndex a where
    deBruijnIndex :: a -> Int
    deBruijnIndexMax :: Proxy a -> Int

instance DeBruijnIndex EmptyScope where
    deBruijnIndex = \case
    deBruijnIndexMax _ = -1

instance DeBruijnIndex a => DeBruijnIndex (Maybe a) where
    deBruijnIndex Nothing = 0
    deBruijnIndex (Just x) = 1 + deBruijnIndex x
    deBruijnIndexMax _ = 1 + deBruijnIndexMax (Proxy :: Proxy a)

inverseDeBruijnIndex :: forall a. DeBruijnIndex a => a -> Int
inverseDeBruijnIndex x = deBruijnIndexMax (Proxy :: Proxy a) - deBruijnIndex x

type ScopeTypes v t = IntMap (Node (UTerm v) t)

class HasScopeTypes v t env where
    scopeTypes :: Lens' env (ScopeTypes v t)

instance HasScopeTypes v t (ScopeTypes v t) where
    scopeTypes = id

type instance TypeAST (Scope t k) = TypeAST (t k)
type instance TypeAST (ScopeVar t k) = TypeAST (t k)
instance HasTypeAST1 t => HasTypeAST1 (Scope t) where
    type TypeAST1 (Scope t) = TypeAST1 t
    type TypeASTIndexConstraint (Scope t) = DeBruijnIndex
    typeAst _ p = withDict (typeAst (Proxy :: Proxy t) p) Dict
instance HasTypeAST1 t => HasTypeAST1 (ScopeVar t) where
    type TypeAST1 (ScopeVar t) = TypeAST1 t
    type TypeASTIndexConstraint (ScopeVar t) = DeBruijnIndex
    typeAst _ p = withDict (typeAst (Proxy :: Proxy t) p) Dict

instance
    ( HasTypeAST1 t
    , FuncType (TypeAST1 t)
    , InferMonad1 m t
    , UnifyMonad m (TypeAST (t k))
    , TypeASTIndexConstraint t ~ DeBruijnIndex
    , DeBruijnIndex k
    , MonadReader env m
    , HasScopeTypes (Var m) (TypeAST1 t) env
    ) =>
    InferMonad m (Scope t k) where

    infer (Scope (Identity x)) =
        do
            varType <- newVar (binding :: Binding m (TypeAST (t k)))
            withDict (typeAst pt pk)
                (local
                    (scopeTypes . Lens.at (deBruijnIndexMax (Proxy :: Proxy (Maybe k))) ?~ varType)
                    (withDict (sameTypeAst pt pk (Proxy :: Proxy (Maybe k)))
                        (infer x)
                        \\ (inferMonad :: DeBruijnIndex (Maybe k) :- InferMonad m (t (Maybe k)))
                    )
                    <&> (funcType #) . (,) varType
                ) <&> UTerm
        where
            pt = Proxy :: Proxy t
            pk = Proxy :: Proxy k

instance
    ( UnifyMonad m (TypeAST (t k))
    , MonadReader env m
    , HasScopeTypes (Var m) (TypeAST (t k)) env
    , DeBruijnIndex k
    ) =>
    InferMonad m (ScopeVar t k) where

    infer (ScopeVar var) =
        Lens.view (scopeTypes . Lens.at (inverseDeBruijnIndex var))
        <&> fromMaybe (error "name error")
