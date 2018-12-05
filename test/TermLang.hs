{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, LambdaCase, MultiParamTypeClasses, FlexibleInstances #-}

module TermLang where

import TypeLang

import AST
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
    | EApp (Node f (Term v)) (Node f (Term v))
    | ELit Int

makeChildren [''Term]
instance ChildrenRecursive (Term v)

type instance TypeAST (Term k) = Typ

instance HasTypeAST1 Term where
    type TypeAST1 Term = Typ
    typeAst _ _ = Dict

instance
    (MonadReader env m, HasVarTypes (Var m) Typ env, UnifyMonad m Typ) =>
    InferMonad1 m Term where
    inferMonad = Sub Dict

instance
    (DeBruijnIndex k, MonadReader env m, HasVarTypes (Var m) Typ env, UnifyMonad m Typ) =>
    InferMonad m (Term k) where

    infer ELit{} = UTerm TInt & pure
    infer (EVar var) = infer var
    infer (ELam x) = infer x
    infer (EApp (Identity func) (Identity arg)) =
        do
            argType <- infer arg
            infer func
                >>=
                \case
                UTerm (TFun funcArg funcRes) ->
                    -- Func already inferred to be function,
                    -- skip creating new variable for result for faster inference.
                    funcRes <$ unify funcArg argType
                x ->
                    do
                        funcRes <- newVar binding
                        funcRes <$ unify x (UTerm (TFun argType funcRes))
