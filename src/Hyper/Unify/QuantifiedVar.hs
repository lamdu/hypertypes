-- | A class for types that have quantified variables.

{-# LANGUAGE UndecidableInstances, FlexibleInstances, FlexibleContexts #-}

module Hyper.Unify.QuantifiedVar
    ( HasQuantifiedVar(..)
    , MonadQuantify(..)
    , OrdQVar
    ) where

import Hyper.Knot (Knot)
import Control.Lens (Prism')
import Data.Kind (Type)

import Prelude.Compat

-- | Class for types which have quantified variables
class HasQuantifiedVar (t :: Knot -> Type) where
    -- | The type of quantified variable identifiers
    type family QVar t :: Type
    -- | A `Prism'` from a type to its quantified variable term
    quantifiedVar :: Prism' (t f) (QVar t)

-- | A constraint synonym that represents that
-- the quantified variable of a type has an 'Ord' instance
class    (HasQuantifiedVar t, Ord (QVar t)) => OrdQVar t
instance (HasQuantifiedVar t, Ord (QVar t)) => OrdQVar t

-- | A monad where new quantified variables can be generated
class MonadQuantify typeConstraints q m where
    newQuantifiedVariable :: typeConstraints -> m q
