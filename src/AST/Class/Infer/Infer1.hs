{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators, DataKinds #-}

-- | `Infer` for indexed AST types (such as `AST.Term.Scope.Scope`)

module AST.Class.Infer.Infer1
    ( HasTypeOf1(..), Infer1(..)
    ) where

import AST.Class.Infer (Infer, TypeOf)
import AST.Knot (Knot)
import Data.Constraint (Constraint, Dict, (:-))
import Data.Proxy (Proxy(..))

class HasTypeOf1 t where
    type family TypeOf1 t :: Knot -> *
    type family TypeOfIndexConstraint t :: * -> Constraint
    typeAst :: Proxy (t k) -> Dict (TypeOf (t k) ~ TypeOf1 t)

class HasTypeOf1 t => Infer1 m t where
    inferMonad :: TypeOfIndexConstraint t i :- Infer m (t i)
