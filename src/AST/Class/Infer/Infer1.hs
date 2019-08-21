-- | `Infer` for indexed AST types (such as `AST.Term.Scope.Scope`)

{-# LANGUAGE RankNTypes #-}

module AST.Class.Infer.Infer1
    ( HasTypeOf1(..), HasInferOf1(..), Infer1(..)
    ) where

import AST.Infer
import AST.Knot (Knot)
import Data.Kind (Type, Constraint)
import Data.Proxy (Proxy(..))

class HasTypeOf1 t where
    type family TypeOf1 t :: Knot -> Type
    typeAst ::
        Proxy (t k) ->
        ((TypeOf (t k) ~ TypeOf1 t) => r) ->
        r

class HasInferOf1 t where
    type family InferOf1 t :: Knot -> Type
    type family InferOf1IndexConstraint t :: Type -> Constraint
    hasInferOf1 ::
        Proxy (t k) ->
        ((InferOf (t k) ~ InferOf1 t, Inferrable (t k)) => r) ->
        r

class HasInferOf1 t => Infer1 m t where
    inferMonad ::
        InferOf1IndexConstraint t i =>
        Proxy (Infer m (t i)) ->
        (Infer m (t i) => r) ->
        r
