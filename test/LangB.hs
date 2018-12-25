{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, TypeFamilies, FlexibleInstances, UndecidableInstances, TupleSections, ScopedTypeVariables #-}

module LangB where

import TypeLang

import AST
import AST.Class.Infer
import AST.Unify
import AST.Term.Apply
import AST.Term.Lam
import AST.Term.Let
import AST.Term.Var
import Control.Lens.Operators
import Control.Lens.Tuple
import Data.Constraint

data LangB k
    = BLit Int
    | BApp (Apply LangB k)
    | BVar (Var String LangB k)
    | BLam (Lam String LangB k)
    | BLet (Let String LangB k)

makeChildrenRecursive [''LangB]

type instance TypeAST LangB = Typ

instance (MonadInfer m, MonadScopeTypes [Char] Typ m, Recursive (Unify m) Typ) => Infer m LangB where
    infer (BLit x) =
        withDict (recursive :: RecursiveDict (Unify m) Typ) $
        newTerm TInt <&> (, BLit x)
    infer (BApp x) = infer x <&> _2 %~ BApp
    infer (BVar x) = infer x <&> _2 %~ BVar
    infer (BLam x) = infer x <&> _2 %~ BLam
    infer (BLet x) = infer x <&> _2 %~ BLet
