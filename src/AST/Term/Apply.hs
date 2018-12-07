{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, TupleSections, StandaloneDeriving, DeriveGeneric #-}

module AST.Term.Apply
    ( Apply(..), applyFunc, applyArg
    ) where

import           AST.Class.TH (makeChildrenAndZipMatch)
import           AST.Functor.UTerm (UTerm(..), _UTerm)
import           AST.Infer (InferMonad(..), inferNode, nodeType, TypeAST, FuncType(..))
import           AST.Node (Node)
import           AST.Unify (UnifyMonad(..), Binding(..), unify)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           GHC.Generics (Generic)

import           Prelude.Compat

data Apply expr f = Apply
    { _applyFunc :: Node f expr
    , _applyArg :: Node f expr
    } deriving Generic

deriving instance Eq   (Node f expr) => Eq   (Apply expr f)
deriving instance Ord  (Node f expr) => Ord  (Apply expr f)
deriving instance Show (Node f expr) => Show (Apply expr f)
instance (Binary (Node f expr)) => Binary (Apply expr f)
instance (NFData (Node f expr)) => NFData (Apply expr f)

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
