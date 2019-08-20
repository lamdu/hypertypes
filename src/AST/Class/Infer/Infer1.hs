-- | `Infer` for indexed AST types (such as `AST.Term.Scope.Scope`)

{-# LANGUAGE TypeOperators #-}

module AST.Class.Infer.Infer1
    ( HasTypeOf1(..), HasInferOf1(..), Infer1(..)
    ) where

import AST.Infer
import AST.Knot (Knot)
import Data.Constraint (Constraint, Dict, (:-))
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

class HasTypeOf1 t where
    type family TypeOf1 t :: Knot -> Type
    type family TypeOfIndexConstraint t :: Type -> Constraint
    typeAst :: Proxy (t k) -> Dict (TypeOf (t k) ~ TypeOf1 t)

class HasInferOf1 t where
    type family InferOf1 t :: Knot -> Type
    type family InferOf1IndexConstraint t :: Type -> Constraint
    hasInferOf1 :: Proxy (t k) -> Dict (InferOf (t k) ~ InferOf1 t, Inferrable (t k))

class HasInferOf1 t => Infer1 m t where
    inferMonad :: TypeOfIndexConstraint t i :- Infer m (t i)
