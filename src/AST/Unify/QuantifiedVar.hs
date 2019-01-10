{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, FlexibleContexts #-}

module AST.Unify.QuantifiedVar
    ( HasQuantifiedVar(..)
    ) where

import AST.Knot (Knot)
import Control.Lens (Prism')

import Prelude.Compat

class Ord (QVar t) => HasQuantifiedVar (t :: Knot -> *) where
    type family QVar t
    quantifiedVar :: Prism' (t f) (QVar t)
