{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A type for unification errors
module Hyper.Unify.Error
    ( UnifyError (..)
    , _SkolemUnified
    , _SkolemEscape
    , _ConstraintsViolation
    , _Occurs
    , _Mismatch
    ) where

import Generics.Constraints (Constraints)
import Hyper
import Hyper.Unify.Constraints (TypeConstraintsOf)
import Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import Text.PrettyPrint.HughesPJClass (Pretty (..), maybeParens)

import Hyper.Internal.Prelude

-- | An error that occurred during unification
data UnifyError t h
    = -- | A universally quantified variable was unified with a
      -- different type
      SkolemUnified (h :# t) (h :# t)
    | -- | A universally quantified variable escapes its scope
      SkolemEscape (h :# t)
    | -- | A term violates constraints that should apply to it
      ConstraintsViolation (t h) (TypeConstraintsOf t)
    | -- | Infinite type encountered. A type occurs within itself
      Occurs (t h) (t h)
    | -- | Unification between two mismatching type structures
      Mismatch (t h) (t h)
    deriving (Generic)

makePrisms ''UnifyError
makeCommonInstances [''UnifyError]
makeHTraversableAndBases ''UnifyError

instance Constraints (UnifyError t h) Pretty => Pretty (UnifyError t h) where
    pPrintPrec lvl p =
        maybeParens haveParens . \case
            SkolemUnified x y -> Pretty.text "SkolemUnified" <+> r x <+> r y
            SkolemEscape x -> Pretty.text "SkolemEscape:" <+> r x
            Mismatch x y -> Pretty.text "Mismatch" <+> r x <+> r y
            Occurs x y -> r x <+> Pretty.text "occurs in itself, expands to:" <+> right y
            ConstraintsViolation x y -> Pretty.text "ConstraintsViolation" <+> r x <+> r y
        where
            haveParens = p > 10
            right
                | haveParens = pPrintPrec lvl 0
                | otherwise = pPrintPrec lvl p
            r :: Pretty a => a -> Pretty.Doc
            r = pPrintPrec lvl 11
