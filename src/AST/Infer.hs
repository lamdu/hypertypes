{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, TypeOperators #-}

module AST.Infer
    ( TypeAST, InferMonad(..)
    , HasTypeAST1(..), sameTypeAst, InferMonad1(..)
    , FuncType(..)
    ) where

import           AST (Node)
import           AST.Unify (UnifyMonad(..), UNode)
import           Control.Lens (Prism')
import           Data.Constraint
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))

type family TypeAST (t :: (* -> *) -> *) :: (* -> *) -> *

class UnifyMonad m (TypeAST t) => InferMonad m t where
    infer :: t Identity -> m (UNode m (TypeAST t))

class HasTypeAST1 t where
    type family TypeAST1 t :: (* -> *) -> *
    type family TypeASTIndexConstraint t :: * -> Constraint
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
    inferMonad :: TypeASTIndexConstraint t i :- InferMonad m (t i)

class FuncType t where
    funcType :: Prism' (t f) (Node f t, Node f t)
