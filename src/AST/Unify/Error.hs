{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving #-}

module AST.Unify.Error
    ( UnifyError(..)
    , _SkolemUnified, _SkolemEscape, _ConstraintsMismatch
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

data UnifyError t k
    = SkolemUnified (Tie k t) (Tie k t)
    | SkolemEscape (Tie k t)
    | ConstraintsMismatch (t k) (TypeConstraintsOf t)
    | Occurs (t k) (t k)
    | Mismatch (t k) (t k)
makePrisms ''UnifyError
makeChildren ''UnifyError

type Deps c t k = ((c (Tie k t), c (t k), c (TypeConstraintsOf t)) :: Constraint)

instance Deps Pretty t k => Pretty (UnifyError t k) where
    pPrint (SkolemUnified x y) = Pretty.text "SkolemUnified" <+> pPrint x <+> pPrint y
    pPrint (SkolemEscape x) = Pretty.text "SkolemEscape" <+> pPrint x
    pPrint (ConstraintsMismatch x y) = Pretty.text "ConstraintsMismatch" <+> pPrint x <+> pPrint y
    pPrint (Mismatch x y) = Pretty.text "Mismatch" <+> pPrint x <+> pPrint y
    pPrint (Occurs x y) =
        pPrint x <+> Pretty.text "occurs in itself, expands to:" <+> pPrint y

deriving instance Deps Eq t k => Eq (UnifyError t k)
