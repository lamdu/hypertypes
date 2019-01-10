{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module AST.Unify.QuantifiedVar
    ( HasQuantifiedVar(..)
    , MonadQuantify(..)
    ) where

import AST.Knot (Knot)
import Control.Lens (Prism')

import Prelude.Compat

class Ord (QVar t) => HasQuantifiedVar (t :: Knot -> *) where
    type family QVar t
    quantifiedVar :: Prism' (t f) (QVar t)

class MonadQuantify typeConstraints q m where
    newQuantifiedVariable :: typeConstraints -> m q
