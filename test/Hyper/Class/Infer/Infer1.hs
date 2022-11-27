-- | 'Infer' for indexed AST types (such as 'Hyper.Type.AST.Scope.Scope')
module Hyper.Class.Infer.Infer1
    ( HasTypeOf1 (..)
    , HasInferOf1 (..)
    , Infer1 (..)
    ) where

import Data.Constraint (Constraint, Dict, (:-))
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Hyper.Infer
import Hyper.Type (HyperType)

class HasTypeOf1 t where
    type TypeOf1 t :: HyperType
    typeAst :: Proxy (t h) -> Dict (TypeOf (t h) ~ TypeOf1 t)

class HasInferOf1 t where
    type InferOf1 t :: HyperType
    type InferOf1IndexConstraint t :: Type -> Constraint
    hasInferOf1 :: Proxy (t h) -> Dict (InferOf (t h) ~ InferOf1 t)

class HasInferOf1 t => Infer1 m t where
    inferMonad :: InferOf1IndexConstraint t i :- Infer m (t i)
