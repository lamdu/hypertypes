{-# LANGUAGE NoImplicitPrelude, TypeFamilies, DataKinds, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module AST.Class.Unify
    ( Unify(..), UVar
    ) where

import AST.Class.ZipMatch (ZipMatch)
import AST.Knot (Tree, Knot)
import AST.Unify.Binding (Binding)
import AST.Unify.Error (UnifyError(..))
import AST.Unify.Constraints (HasTypeConstraints(..), ScopeConstraintsMonad)
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify)
import AST.Unify.Term (UTermBody, uBody)
import Control.Lens.Operators

import Prelude.Compat

-- Unification variable type for a unification monad
type family UVar (m :: * -> *) :: Knot -> *

class
    ( Eq (Tree (UVar m) t)
    , ZipMatch t
    , HasTypeConstraints t
    , HasQuantifiedVar t
    , ScopeConstraintsMonad (TypeConstraintsOf t) m
    , MonadQuantify (TypeConstraintsOf t) (QVar t) m
    ) => Unify m t where

    binding :: Binding (UVar m) m t

    unifyError :: Tree (UnifyError t) (UVar m) -> m ()

    -- | What to do when top-levels of terms being unified do not match.
    -- Usually this will throw a failure,
    -- but some AST terms could be equivalent despite not matching,
    -- like record extends with fields ordered differently,
    -- and these could still match.
    structureMismatch :: Tree (UTermBody (UVar m)) t -> Tree (UTermBody (UVar m)) t -> m ()
    structureMismatch x y = unifyError (Mismatch (x ^. uBody) (y ^. uBody))
