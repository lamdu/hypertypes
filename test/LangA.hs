{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, LambdaCase, MultiParamTypeClasses, FlexibleInstances, DataKinds, TupleSections, ScopedTypeVariables, ConstraintKinds, FlexibleContexts #-}

-- | A test language with locally-nameless variable scoping and type signatures with for-alls

module LangA where

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

data LangA v f
    = ALam (Scope LangA v f)
    | AVar (ScopeVar LangA v f)
    | AApp (Apply (LangA v) f)
    | ATypeSig (TypeSig (Tree Pure (Scheme Types Typ)) (LangA v) f)
    | ALit Int

makeChildrenRecursive [''LangA]
instance Recursive Children (LangA v)

type instance TypeAST (LangA k) = Typ

instance HasTypeAST1 LangA where
    type TypeAST1 LangA = Typ
    type TypeASTIndexConstraint LangA = DeBruijnIndex
    typeAst _ = Dict

type TermInfer1Deps env m =
    ( MonadInfer m
    , MonadReader env m
    , HasScopeTypes (UniVar m) Typ env
    , Recursive (Unify m) Typ
    , Recursive (CanInstantiate m Types) Typ
    , ChildrenConstraint Types (Unify m)
    )

instance TermInfer1Deps env m => Infer1 m LangA where
    inferMonad = Sub Dict

instance (DeBruijnIndex k, TermInfer1Deps env m) => Infer m (LangA k) where
    infer (ALit x) =
        withDict (recursive :: RecursiveDict (Unify m) Typ) $
        newTerm TInt <&> (, ALit x)
    infer (AVar     x) = infer x <&> _2 %~ AVar
    infer (ALam     x) = infer x <&> _2 %~ ALam
    infer (AApp     x) = infer x <&> _2 %~ AApp
    infer (ATypeSig x) = infer x <&> _2 %~ ATypeSig
