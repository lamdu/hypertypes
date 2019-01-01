{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators, DataKinds #-}

-- | `Infer` for indexed AST types (such as `AST.Term.Scope.Scope`)

module AST.Class.Infer.Infer1
    ( HasTypeAST1(..), Infer1(..)
    ) where

import AST.Class.Infer (Infer, TypeAST)
import AST.Knot (Knot)
import Data.Constraint (Constraint, Dict, (:-))
import Data.Proxy (Proxy(..))

class HasTypeAST1 t where
    type family TypeAST1 t :: Knot -> *
    type family TypeASTIndexConstraint t :: * -> Constraint
    typeAst :: Proxy (t k) -> Dict (TypeAST (t k) ~ TypeAST1 t)

class HasTypeAST1 t => Infer1 m t where
    inferMonad :: TypeASTIndexConstraint t i :- Infer m (t i)
