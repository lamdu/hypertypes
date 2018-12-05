{-# LANGUAGE NoImplicitPrelude, KindSignatures, TypeFamilies, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, UndecidableInstances, TypeOperators #-}

module AST.Infer
    ( TypeAST, InferMonad(..)
    , HasTypeAST1(..), sameTypeAst, InferMonad1(..)
    , VarTypes, HasVarTypes(..)
    , FuncType(..)
    ) where

import           AST (Node)
import           AST.Scope (Scope(..), ScopeVar(..), DeBruijnIndex(..), inverseDeBruijnIndex)
import           AST.Unify (UnifyMonad(..), Binding(..), UNode, Var)
import           AST.UTerm (UTerm(..))
import           Control.Lens (Lens', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader (MonadReader, local)
import           Data.Constraint
import           Data.Functor.Identity (Identity(..))
import           Data.IntMap (IntMap)
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

type family TypeAST (t :: (* -> *) -> *) :: (* -> *) -> *

class UnifyMonad m (TypeAST t) => InferMonad m t where
    infer :: t Identity -> m (UNode m (TypeAST t))

class HasTypeAST1 t where
    type family TypeAST1 t :: (* -> *) -> *
    typeAst :: Proxy t -> Proxy k -> Dict (TypeAST (t k) ~ TypeAST1 t)

sameTypeAst ::
    HasTypeAST1 t =>
    Proxy t ->
    Proxy k0 ->
    Proxy k1 ->
    Dict (TypeAST (t k0) ~ TypeAST (t k1))
sameTypeAst pt p0 p1 =
    withDict (typeAst pt p0) (withDict (typeAst pt p1) Dict)

class HasTypeAST1 t => InferMonad1 m t where
    inferMonad :: DeBruijnIndex k :- InferMonad m (t k)

type instance TypeAST (Scope t k) = TypeAST (t k)
type instance TypeAST (ScopeVar t k) = TypeAST (t k)
instance HasTypeAST1 t => HasTypeAST1 (Scope t) where
    type TypeAST1 (Scope t) = TypeAST1 t
    typeAst _ p = withDict (typeAst (Proxy :: Proxy t) p) Dict
instance HasTypeAST1 t => HasTypeAST1 (ScopeVar t) where
    type TypeAST1 (ScopeVar t) = TypeAST1 t
    typeAst _ p = withDict (typeAst (Proxy :: Proxy t) p) Dict

type VarTypes v t = IntMap (Node (UTerm v) t)

class HasVarTypes v t env where
    varTypes :: Lens' env (VarTypes v t)

instance HasVarTypes v t (VarTypes v t) where
    varTypes = id

class FuncType t where
    funcType :: Prism' (t f) (Node f t, Node f t)

instance
    ( HasTypeAST1 t
    , FuncType (TypeAST1 t)
    , InferMonad1 m t
    , UnifyMonad m (TypeAST (t k))
    , DeBruijnIndex k
    , MonadReader env m
    , HasVarTypes (Var m) (TypeAST1 t) env
    ) =>
    InferMonad m (Scope t k) where

    infer (Scope (Identity x)) =
        do
            varType <- newVar (binding :: Binding m (TypeAST (t k)))
            withDict (typeAst pt pk)
                (local
                    (varTypes . Lens.at (deBruijnIndexMax (Proxy :: Proxy (Maybe k))) ?~ varType)
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
    , HasVarTypes (Var m) (TypeAST (t k)) env
    , DeBruijnIndex k
    ) =>
    InferMonad m (ScopeVar t k) where

    infer (ScopeVar var) =
        Lens.view (varTypes . Lens.at (inverseDeBruijnIndex var))
        <&> fromMaybe (error "name error")
