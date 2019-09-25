-- | 'Infer' for indexed AST types (such as 'Hyper.Term.Scope.Scope')

module Hyper.Class.Infer.Infer1
    ( HasTypeOf1(..), HasInferOf1(..), Infer1(..)
    ) where

import Hyper.Infer
import Hyper.Type (HyperType)
import Data.Constraint (Constraint, Dict, (:-))
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

class HasTypeOf1 t where
    type family TypeOf1 t :: HyperType
    typeAst :: Proxy (t k) -> Dict (TypeOf (t k) ~ TypeOf1 t)

class HasInferOf1 t where
    type family InferOf1 t :: HyperType
    type family InferOf1IndexConstraint t :: Type -> Constraint
    hasInferOf1 :: Proxy (t k) -> Dict (InferOf (t k) ~ InferOf1 t)

class HasInferOf1 t => Infer1 m t where
    inferMonad :: InferOf1IndexConstraint t i :- Infer m (t i)
