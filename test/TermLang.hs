{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, LambdaCase, MultiParamTypeClasses, FlexibleInstances, DataKinds, TupleSections, ScopedTypeVariables, ConstraintKinds, FlexibleContexts #-}

module TermLang where

import TypeLang

import AST
import AST.Class.Infer
import AST.Class.Infer.Infer1
import AST.Term.Apply
import AST.Term.Scheme
import AST.Term.Scope
import AST.Term.TypeSig
import AST.Unify
import Control.Lens.Operators
import Control.Lens.Tuple
import Control.Monad.Reader
import Data.Constraint

data Term v f
    = ELam (Scope Term v f)
    | EVar (ScopeVar Term v f)
    | EApp (Apply (Term v) f)
    | ETypeSig (TypeSig (Tree Pure (Scheme Types Typ)) (Term v) f)
    | ELit Int

makeChildrenRecursive [''Term]
instance Recursive Children (Term v)

type instance TypeAST (Term k) = Typ

instance HasTypeAST1 Term where
    type TypeAST1 Term = Typ
    type TypeASTIndexConstraint Term = DeBruijnIndex
    typeAst _ = Dict

type TermInfer1Deps env m =
    ( MonadReader env m
    , HasScopeTypes (UniVar m) Typ env
    , Recursive (Unify m) Typ
    , Recursive (CanInstantiate m Types) Typ
    , ChildrenConstraint Types (Unify m)
    )

instance TermInfer1Deps env m => Infer1 m Term where
    inferMonad = Sub Dict

instance (DeBruijnIndex k, TermInfer1Deps env m) => Infer m (Term k) where
    infer (ELit x) =
        withDict (recursive :: RecursiveDict (Unify m) Typ) $
        newTerm TInt <&> (, ELit x)
    infer (EVar     x) = infer x <&> _2 %~ EVar
    infer (ELam     x) = infer x <&> _2 %~ ELam
    infer (EApp     x) = infer x <&> _2 %~ EApp
    infer (ETypeSig x) = infer x <&> _2 %~ ETypeSig
