{-# LANGUAGE FlexibleContexts, RankNTypes, DefaultSignatures #-}
{-# OPTIONS -Wno-redundant-constraints #-} -- Work around false GHC warnings

module AST.Class.Unify
    ( Unify(..), UVarOf
    , BindingDict(..)
    ) where

import AST.Class.Nodes (KNodes(..))
import AST.Class.Recursive
import AST.Class.ZipMatch (ZipMatch)
import AST.Knot (Tree, Knot)
import AST.Unify.Error (UnifyError(..))
import AST.Unify.Constraints
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify)
import AST.Unify.Term (UTerm, UTermBody, uBody)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))
import Data.Kind (Type)

import Prelude.Compat

-- Unification variable type for a unification monad
type family UVarOf (m :: Type -> Type) :: Knot -> Type

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
    , RTraversable t
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
        (forall c. Unify m c => Tree (UVarOf m) c -> Tree (UVarOf m) c -> m (Tree (UVarOf m) c)) ->
        Tree (UTermBody (UVarOf m)) t -> Tree (UTermBody (UVarOf m)) t -> m ()
    structureMismatch _ x y = unifyError (Mismatch (x ^. uBody) (y ^. uBody))

    unifyRecursive ::
        Proxy m -> Proxy t -> (NodesConstraint t (Unify m) => r) -> r
    {-# INLINE unifyRecursive #-}
    default unifyRecursive ::
        NodesConstraint t (Unify m) =>
        Proxy m -> Proxy t -> (NodesConstraint t (Unify m) => r) -> r
    unifyRecursive _ _ = id

instance Recursive (Unify m) where
    {-# INLINE recurse #-}
    recurse =
        unifyRecursive (Proxy @m) . p
        where
            p :: Proxy (Unify m t) -> Proxy t
            p _ = Proxy
