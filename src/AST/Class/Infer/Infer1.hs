{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, TypeOperators #-}

-- | `Infer` for indexed AST types (such as `AST.Term.Scope.Scope`)

module AST.Class.Infer.Infer1
    ( HasTypeAST1(..), Infer1(..)
    ) where

import           AST.Class.Infer
import           Data.Constraint
import           Data.Proxy (Proxy(..))

class HasTypeAST1 t where
    type family TypeAST1 t :: (* -> *) -> *
    type family TypeASTIndexConstraint t :: * -> Constraint
    typeAst :: Proxy (t k) -> Dict (TypeAST (t k) ~ TypeAST1 t)

class HasTypeAST1 t => Infer1 m t where
    inferMonad :: TypeASTIndexConstraint t i :- Infer m (t i)
