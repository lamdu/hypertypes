{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, LambdaCase, MultiParamTypeClasses, FlexibleInstances #-}

module TermLang where

import TypeLang

import AST
import AST.Class.Infer
import AST.Class.Infer.Infer1
import AST.Functor.UTerm
import AST.Term.Apply
import AST.Term.Scope
import AST.Unify
import Control.Lens.Operators
import Control.Lens.Tuple
import Control.Monad.Reader
import Data.Constraint

data Term v f
    = ELam (Scope Term v f)
    | EVar (ScopeVar Term v f)
    | EApp (Apply (Term v) f)
    | ELit Int

makeChildren [''Term]
instance Recursive Children (Term v)

type instance TypeAST (Term k) = Typ

instance HasTypeAST1 Term where
    type TypeAST1 Term = Typ
    type TypeASTIndexConstraint Term = DeBruijnIndex
    typeAst _ = Dict

instance
    (MonadReader env m, HasScopeTypes (UniVar m) Typ env, Recursive (Unify m) Typ, MonadUnify m) =>
    Infer1 m Term where
    inferMonad = Sub Dict

instance
    (DeBruijnIndex k, MonadReader env m, HasScopeTypes (UniVar m) Typ env, Recursive (Unify m) Typ, MonadUnify m) =>
    Infer m (Term k) where

    infer (ELit x) = pure (UTerm TInt, ELit x)
    infer (EVar x) = infer x <&> _2 %~ EVar
    infer (ELam x) = infer x <&> _2 %~ ELam
    infer (EApp x) = infer x <&> _2 %~ EApp
