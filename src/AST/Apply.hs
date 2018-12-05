{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}

module AST.Apply
    ( Apply(..), applyFunc, applyArg
    ) where

import           AST (Node)
import           AST.Infer (InferMonad(..), TypeAST, FuncType(..))
import           AST.Unify (UnifyMonad(..), Binding(..), unify)
import           AST.UTerm (UTerm(..), _UTerm)
import           AST.TH (makeChildrenAndZipMatch)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Functor.Identity (Identity(..))

import           Prelude.Compat

data Apply expr f = Apply
    { _applyFunc :: Node f expr
    , _applyArg :: Node f expr
    }

Lens.makeLenses ''Apply
makeChildrenAndZipMatch [''Apply]

type instance TypeAST (Apply expr) = TypeAST expr

instance (InferMonad m expr, FuncType (TypeAST expr)) => InferMonad m (Apply expr) where
    infer (Apply (Identity func) (Identity arg)) =
        do
            argType <- infer arg
            funcT <- infer func
            case funcT ^? _UTerm . funcType of
                Just (funcArg, funcRes) ->
                    -- Func already inferred to be function,
                    -- skip creating new variable for result for faster inference.
                    funcRes <$ unify funcArg argType
                Nothing ->
                    do
                        funcRes <- newVar binding
                        funcRes <$ unify funcT (UTerm (funcType # (argType, funcRes)))
