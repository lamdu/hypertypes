{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, TypeOperators #-}

module AST.Infer
    ( TypeAST, InferMonad(..)
    , HasTypeAST1(..), InferMonad1(..)
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
    typeAst :: Proxy (t k) -> Dict (TypeAST (t k) ~ TypeAST1 t)

class HasTypeAST1 t => InferMonad1 m t where
    inferMonad :: TypeASTIndexConstraint t i :- InferMonad m (t i)

class FuncType t where
    funcType :: Prism' (t f) (Node f t, Node f t)
