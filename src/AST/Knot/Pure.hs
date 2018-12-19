{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, TypeFamilies #-}

module AST.Knot.Pure
    ( Pure(..)
    ) where

import AST.Class.Children (Children(..))
import AST.Class.Children.Mono (ChildOf)
import AST.Knot (Tie)
import Control.Lens.Operators

import Prelude.Compat

newtype Pure k = Pure { getPure :: Tie k Pure }

instance Children Pure where
    type SubTreeConstraint Pure k constraint = constraint (Tie k Pure)
    type ChildrenConstraint Pure constraint = constraint Pure
    children _ f (Pure x) = f x <&> Pure

type instance ChildOf Pure = Pure

deriving instance SubTreeConstraint Pure f Eq   => Eq   (Pure f)
deriving instance SubTreeConstraint Pure f Ord  => Ord  (Pure f)

instance SubTreeConstraint Pure f Show => Show (Pure f) where
    showsPrec p (Pure x) =
        -- TODO: How to make a proper show instance without extra parens?
        -- (Not using the built-in one because of the large record syntax)
        showParen (p > 0) (\rest -> "Pure (" <> show x <> ")" <> rest)
