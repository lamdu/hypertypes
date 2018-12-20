{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, TypeFamilies, TemplateHaskell #-}

module AST.Knot.Pure
    ( Pure(..)
    ) where

import AST.Class.Children (Children(..))
import AST.Class.Children.TH
import AST.Knot (Tie)

import Prelude.Compat

newtype Pure k = Pure { getPure :: Tie k Pure }

makeChildren ''Pure

deriving instance SubTreeConstraint Pure f Eq   => Eq   (Pure f)
deriving instance SubTreeConstraint Pure f Ord  => Ord  (Pure f)

instance SubTreeConstraint Pure f Show => Show (Pure f) where
    -- TODO: Couldn't get x to only have parens when needed..
    showsPrec p (Pure x) = showParen (p > 0) (("Pure (" <>) . shows x . (")" <>))
