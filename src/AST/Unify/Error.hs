{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module AST.Unify.Error
    ( UnifyError(..)
    , _SkolemUnified, _SkolemEscape, _ConstraintsViolation
    , _Occurs, _Mismatch
    ) where

import           AST
import           AST.TH.Internal.Instances (makeCommonInstances)
import           AST.TH.Functor (makeKFunctor)
import           AST.TH.Traversable (makeKTraversableAndFoldable)
import           AST.Unify.Constraints (TypeConstraintsOf)
import           Control.Lens (makePrisms)
import           Generics.Constraints (Constraints)
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | An error that occurred during unification
data UnifyError t k
    = SkolemUnified (k # t) (k # t)
      -- ^ A universally quantified variable was unified with a
      -- different type
    | SkolemEscape (k # t)
      -- ^ A universally quantified variable escapes its scope
    | ConstraintsViolation (t k) (TypeConstraintsOf t)
      -- ^ A term violates constraints that should apply to it
    | Occurs (t k) (t k)
      -- ^ Infinite type encountered. A type occurs within itself
    | Mismatch (t k) (t k)
      -- ^ Unification between two mismatching type structures
    deriving Generic

makePrisms ''UnifyError
makeCommonInstances [''UnifyError]

-- TODO: TH should be able to generate this
instance KNodes t => KNodes (UnifyError t) where
    type KNodesConstraint (UnifyError t) c = (c t, KNodesConstraint t c)
    data KWitness (UnifyError t) n where
        W_UnifyError_t :: KWitness (UnifyError t) t
        E_UnifyError_t :: KWitness t n -> KWitness (UnifyError t) n
    kLiftConstraint W_UnifyError_t = const id
    kLiftConstraint (E_UnifyError_t w) = kLiftConstraint w

makeKFunctor ''UnifyError
makeKTraversableAndFoldable ''UnifyError

instance Constraints (UnifyError t k) Pretty => Pretty (UnifyError t k) where
    pPrintPrec lvl p =
        maybeParens haveParens . \case
        SkolemUnified x y        -> Pretty.text "SkolemUnified" <+> r x <+> r y
        SkolemEscape x           -> Pretty.text "SkolemEscape:" <+> r x
        Mismatch x y             -> Pretty.text "Mismatch" <+> r x <+> r y
        Occurs x y               -> r x <+> Pretty.text "occurs in itself, expands to:" <+> right y
        ConstraintsViolation x y -> Pretty.text "ConstraintsViolation" <+> r x <+> r y
        where
            haveParens = p > 10
            right
                | haveParens = pPrintPrec lvl 0
                | otherwise = pPrintPrec lvl p
            r :: Pretty a => a -> Pretty.Doc
            r = pPrintPrec lvl 11
