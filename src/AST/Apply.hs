{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TupleSections #-}

module AST.Apply
    ( Apply(..), applyFunc, applyArg
    ) where

import           AST (Node)
import           AST.Infer (InferMonad(..), inferNode, nodeType, TypeAST, FuncType(..))
import           AST.Unify (UnifyMonad(..), Binding(..), unify)
import           AST.UTerm (UTerm(..), _UTerm)
import           AST.TH (makeChildrenAndZipMatch)
import qualified Control.Lens as Lens
import           Control.Lens.Operators

import           Prelude.Compat

data Apply expr f = Apply
    { _applyFunc :: Node f expr
    , _applyArg :: Node f expr
    }

Lens.makeLenses ''Apply
makeChildrenAndZipMatch [''Apply]

type instance TypeAST (Apply expr) = TypeAST expr

instance (InferMonad m expr, FuncType (TypeAST expr)) => InferMonad m (Apply expr) where
    infer (Apply func arg) =
        do
            argI <- inferNode arg
            let argT = argI ^. nodeType
            funcI <- inferNode func
            let funcT = funcI ^. nodeType
            case funcT ^? _UTerm . funcType of
                Just (funcArg, funcRes) ->
                    -- Func already inferred to be function,
                    -- skip creating new variable for result for faster inference.
                    funcRes <$ unify funcArg argT
                Nothing ->
                    do
                        funcRes <- newVar binding
                        funcRes <$ unify funcT (UTerm (funcType # (argT, funcRes)))
                <&> (, Apply funcI argI)
