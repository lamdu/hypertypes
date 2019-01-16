{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving #-}

module AST.Unify.Error
    ( UnifyError(..)
    , _SkolemUnified, _SkolemEscape, _ConstraintsViolation
    , _Occurs, _Mismatch
    ) where

import           AST
import           AST.Unify.Constraints (HasTypeConstraints(..))
import           Control.Lens (makePrisms)
import           Data.Constraint (Constraint)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

-- | An error that occurred during unification
data UnifyError t k
    = SkolemUnified (Tie k t) (Tie k t)
      -- ^ A universally quantified variable was unified with a
      -- different type
    | SkolemEscape (Tie k t)
      -- ^ A universally quantified variable escapes its scope
    | ConstraintsViolation (t k) (TypeConstraintsOf t)
      -- ^ A term violates constraints that should apply to it
    | Occurs (t k) (t k)
      -- ^ Infinite type encountered. A type occurs within itself
    | Mismatch (t k) (t k)
      -- ^ Unification between two mismatching type structures
makePrisms ''UnifyError
makeChildren ''UnifyError

type Deps c t k = ((c (Tie k t), c (t k), c (TypeConstraintsOf t)) :: Constraint)

instance Deps Pretty t k => Pretty (UnifyError t k) where
    pPrint (SkolemUnified x y) = Pretty.text "SkolemUnified" <+> pPrint x <+> pPrint y
    pPrint (SkolemEscape x) = Pretty.text "SkolemEscape" <+> pPrint x
    pPrint (ConstraintsViolation x y) = Pretty.text "ConstraintsViolation" <+> pPrint x <+> pPrint y
    pPrint (Mismatch x y) = Pretty.text "Mismatch" <+> pPrint x <+> pPrint y
    pPrint (Occurs x y) =
        pPrint x <+> Pretty.text "occurs in itself, expands to:" <+> pPrint y

deriving instance Deps Eq t k => Eq (UnifyError t k)
