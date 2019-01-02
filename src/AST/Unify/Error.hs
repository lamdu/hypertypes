{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies #-}

module AST.Unify.Error
    ( UnifyError(..)
    , _SkolemUnified, _SkolemEscape, _ConstraintsMismatch
    , _Occurs, _Mismatch
    ) where

import AST.Class.Children.TH (makeChildren)
import AST.Knot (Tie)
import AST.Unify.Constraints (HasTypeConstraints(..))
import Control.Lens (makePrisms)

data UnifyError t k
    = SkolemUnified (Tie k t) (Tie k t)
    | SkolemEscape (Tie k t)
    | ConstraintsMismatch (t k) (TypeConstraintsOf t)
    | Occurs (t k) (t k)
    | Mismatch (t k) (t k)
makePrisms ''UnifyError
makeChildren ''UnifyError
