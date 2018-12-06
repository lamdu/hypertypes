{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, LambdaCase, MultiParamTypeClasses, FlexibleInstances #-}

module TermLang where

import TypeLang

import AST.Apply
import AST.Infer
import AST.Recursive
import AST.Scope
import AST.TH
import AST.Unify
import AST.UTerm
import Control.Lens.Operators
import Control.Monad.Reader
import Data.Constraint
import Data.Functor.Identity

data Term v f
    = ELam (Scope Term v f)
    | EVar (ScopeVar Term v Identity)
    | EApp (Apply (Term v) f)
    | ELit Int

makeChildren [''Term]
instance ChildrenRecursive (Term v)

type instance TypeAST (Term k) = Typ

instance HasTypeAST1 Term where
    type TypeAST1 Term = Typ
    type TypeASTIndexConstraint Term = DeBruijnIndex
    typeAst _ = Dict

instance
    (MonadReader env m, HasScopeTypes (Var m) Typ env, UnifyMonad m Typ) =>
    InferMonad1 m Term where
    inferMonad = Sub Dict

instance
    (DeBruijnIndex k, MonadReader env m, HasScopeTypes (Var m) Typ env, UnifyMonad m Typ) =>
    InferMonad m (Term k) where

    infer ELit{} = UTerm TInt & pure
    infer (EVar x) = infer x
    infer (ELam x) = infer x
    infer (EApp x) = infer x
