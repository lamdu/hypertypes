{-# LANGUAGE TypeFamilies, UndecidableInstances, UndecidableSuperClasses #-}

module AST where

import GHC.Exts (Constraint)

class ChildrenConstraint expr Children => Children expr where
    type ChildrenConstraint expr (constraint :: ((* -> *) -> *) -> Constraint) :: Constraint
