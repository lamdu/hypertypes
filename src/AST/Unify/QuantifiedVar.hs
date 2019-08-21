{-# LANGUAGE UndecidableInstances, FlexibleInstances, FlexibleContexts #-}

module AST.Unify.QuantifiedVar
    ( HasQuantifiedVar(..)
    , MonadQuantify(..)
    , OrdQVar
    ) where

import AST.Knot (Knot)
import Control.Lens (Prism')
import Data.Kind (Type)

import Prelude.Compat

class HasQuantifiedVar (t :: Knot -> Type) where
    type family QVar t :: Type
    quantifiedVar :: Prism' (t f) (QVar t)

class    (HasQuantifiedVar t, Ord (QVar t)) => OrdQVar t
instance (HasQuantifiedVar t, Ord (QVar t)) => OrdQVar t

class MonadQuantify typeConstraints q m where
    newQuantifiedVariable :: typeConstraints -> m q
