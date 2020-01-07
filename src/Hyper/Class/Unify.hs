-- | A class for unification

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.Unify
    ( Unify(..), UVarOf
    , UnifyGen(..)
    , BindingDict(..)
    ) where

import Data.Kind (Type)
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Class.Recursive
import Hyper.Class.ZipMatch (ZipMatch)
import Hyper.Type (HyperType, type (#))
import Hyper.Unify.Constraints
import Hyper.Unify.Error (UnifyError(..))
import Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify)
import Hyper.Unify.Term (UTerm)

import Hyper.Internal.Prelude

-- | Unification variable type for a unification monad
type family UVarOf (m :: Type -> Type) :: HyperType

-- | BindingDict implements unification variables for a type in a unification monad.
--
-- It is parameterized on:
--
-- * @v@: The unification variable 'HyperType'
-- * @m@: The 'Monad' to bind in
-- * @t@: The unified term's 'HyperType'
--
-- Has 2 implementations in hypertypes:
--
-- * 'Hyper.Unify.Binding.bindingDict' for pure state based unification
-- * 'Hyper.Unify.Binding.ST.stBinding' for 'Control.Monad.ST.ST' based unification
data BindingDict v m t = BindingDict
    { lookupVar :: !(v # t -> m (UTerm v # t))
    , newVar :: !(UTerm v # t -> m (v # t))
    , bindVar :: !(v # t -> UTerm v # t -> m ())
    }

-- | @Unify m t@ enables 'Hyper.Unify.unify' to perform unification for @t@ in the 'Monad' @m@.
--
-- The 'unifyRecursive' method represents the constraint that @Unify m@ applies to all recursive child nodes.
-- It replaces context for 'Unify' to avoid @UndecidableSuperClasses@.
class
    ( Eq (UVarOf m # t)
    , RTraversable t
    , ZipMatch t
    , HasTypeConstraints t
    , HasQuantifiedVar t
    , Monad m
    , MonadQuantify (TypeConstraintsOf t) (QVar t) m
    ) => Unify m t where

    -- | The implementation for unification variables binding and lookup
    binding :: BindingDict (UVarOf m) m t

    -- | Handles a unification error.
    --
    -- If 'unifyError' is called then unification has failed.
    -- A compiler implementation may present an error message based on the provided 'UnifyError' when this occurs.
    unifyError :: UnifyError t # UVarOf m -> m a

    -- | What to do when top-levels of terms being unified do not match.
    --
    -- Usually this will cause a 'unifyError'.
    --
    -- Some AST terms could be equivalent despite not matching structurally,
    -- like record field extentions with the fields ordered differently.
    -- Those would override the default implementation to handle the unification of mismatching structures.
    structureMismatch ::
        (forall c. Unify m c => UVarOf m # c -> UVarOf m # c -> m (UVarOf m # c)) ->
        t # UVarOf m -> t # UVarOf m -> m ()
    structureMismatch _ x y = unifyError (Mismatch x y)

    -- TODO: Putting documentation here causes duplication in the haddock documentation
    unifyRecursive :: Proxy m -> Proxy t -> Dict (HNodesConstraint t (Unify m))
    {-# INLINE unifyRecursive #-}
    default unifyRecursive ::
        HNodesConstraint t (Unify m) =>
        Proxy m -> Proxy t -> Dict (HNodesConstraint t (Unify m))
    unifyRecursive _ _ = Dict

instance Recursive (Unify m) where
    {-# INLINE recurse #-}
    recurse = unifyRecursive (Proxy @m) . proxyArgument

-- | A class for unification monads with scope levels
class Unify m t => UnifyGen m t where
    -- | Get the current scope constraint
    scopeConstraints :: Proxy t -> m (TypeConstraintsOf t)

    unifyGenRecursive :: Proxy m -> Proxy t -> Dict (HNodesConstraint t (UnifyGen m))
    {-# INLINE unifyGenRecursive #-}
    default unifyGenRecursive ::
        HNodesConstraint t (UnifyGen m) =>
        Proxy m -> Proxy t -> Dict (HNodesConstraint t (UnifyGen m))
    unifyGenRecursive _ _ = Dict

instance Recursive (UnifyGen m) where
    {-# INLINE recurse #-}
    recurse = unifyGenRecursive (Proxy @m) . proxyArgument
