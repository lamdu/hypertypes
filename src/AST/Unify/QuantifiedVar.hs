{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, FlexibleInstances #-}

module AST.Unify.QuantifiedVar
    ( HasQuantifiedVar(..)
    , MonadQuantify(..)
    , QVarHasInstance
    ) where

import AST.Knot (Knot)
import Control.Lens (Prism')
import Data.Kind (Type)

class HasQuantifiedVar (t :: Knot -> Type) where
    type family QVar t :: Type
    quantifiedVar :: Prism' (t f) (QVar t)

class    (HasQuantifiedVar t, cls (QVar t)) => QVarHasInstance cls t
instance (HasQuantifiedVar t, cls (QVar t)) => QVarHasInstance cls t

class MonadQuantify typeConstraints q m where
    newQuantifiedVariable :: typeConstraints -> m q
