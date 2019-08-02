{-# LANGUAGE FlexibleContexts, RankNTypes #-}

module AST.Class.Unify
    ( Unify(..), UVarOf
    , BindingDict(..)
    ) where

import AST.Class (KNodes)
import AST.Class.Recursive (Recursively)
import AST.Class.Traversable (KTraversable)
import AST.Class.ZipMatch (ZipMatch)
import AST.Knot (Tree, Knot)
import AST.Unify.Error (UnifyError(..))
import AST.Unify.Constraints (HasTypeConstraints(..), MonadScopeConstraints)
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify)
import AST.Unify.Term (UTerm, UTermBody, uBody)
import Control.Lens.Operators

import Prelude.Compat

-- Unification variable type for a unification monad
type family UVarOf (m :: * -> *) :: Knot -> *

-- | BindingDict, parameterized on:
--
-- * `v`: unification variable type
-- * `m`: monad to bind in
-- * `t`: term type
--
-- Has 2 implementations in syntax-tree:
--
-- * "AST.Unify.Binding.Pure"
-- * "AST.Unify.Binding.ST"
data BindingDict v m t = BindingDict
    { lookupVar :: Tree v t -> m (Tree (UTerm v) t)
    , newVar :: Tree (UTerm v) t -> m (Tree v t)
    , bindVar :: Tree v t -> Tree (UTerm v) t -> m ()
    }

class
    ( Eq (Tree (UVarOf m) t)
    , KNodes t
    , KTraversable t
    , ZipMatch t
    , HasTypeConstraints t
    , HasQuantifiedVar t
    , MonadScopeConstraints (TypeConstraintsOf t) m
    , MonadQuantify (TypeConstraintsOf t) (QVar t) m
    ) => Unify m t where

    binding :: BindingDict (UVarOf m) m t

    unifyError :: Tree (UnifyError t) (UVarOf m) -> m a

    -- | What to do when top-levels of terms being unified do not match.
    -- Usually this will throw a failure,
    -- but some AST terms could be equivalent despite not matching,
    -- like record extends with fields ordered differently,
    -- and these could still match.
    structureMismatch ::
        (forall c. Recursively (Unify m) c => Tree (UVarOf m) c -> Tree (UVarOf m) c -> m (Tree (UVarOf m) c)) ->
        Tree (UTermBody (UVarOf m)) t -> Tree (UTermBody (UVarOf m)) t -> m ()
    structureMismatch _ x y = unifyError (Mismatch (x ^. uBody) (y ^. uBody))
