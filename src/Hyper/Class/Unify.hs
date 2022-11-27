{-# LANGUAGE FlexibleContexts #-}

-- | A class for unification
module Hyper.Class.Unify
    ( Unify (..)
    , UVarOf
    , UnifyGen (..)
    , BindingDict (..)
    , applyBindings
    , semiPruneLookup
    , occursError
    ) where

import Control.Monad (unless)
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Monad.Trans.State (get, put, runStateT)
import Data.Kind (Type)
import Hyper.Class.Nodes (HNodes (..), (#>))
import Hyper.Class.Optic (HSubset (..), HSubset')
import Hyper.Class.Recursive
import Hyper.Class.Traversable (htraverse)
import Hyper.Class.ZipMatch (ZipMatch)
import Hyper.Type (HyperType, type (#))
import Hyper.Type.Pure (Pure, _Pure)
import Hyper.Unify.Constraints
import Hyper.Unify.Error (UnifyError (..))
import Hyper.Unify.QuantifiedVar (HasQuantifiedVar (..), MonadQuantify (..))
import Hyper.Unify.Term (UTerm (..), UTermBody (..), uBody)

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
    ) =>
    Unify m t
    where
    -- | The implementation for unification variables binding and lookup
    binding :: BindingDict (UVarOf m) m t

    -- | Handles a unification error.
    --
    -- If 'unifyError' is called then unification has failed.
    -- A compiler implementation may present an error message based on the provided 'UnifyError' when this occurs.
    unifyError :: UnifyError t # UVarOf m -> m a
    default unifyError ::
        (MonadError (e # Pure) m, HSubset' e (UnifyError t)) =>
        UnifyError t # UVarOf m ->
        m a
    unifyError e =
        htraverse (Proxy @(Unify m) #> applyBindings) e
            >>= throwError . (hSubset #)
                \\ unifyRecursive (Proxy @m) (Proxy @t)

    -- | What to do when top-levels of terms being unified do not match.
    --
    -- Usually this will cause a 'unifyError'.
    --
    -- Some AST terms could be equivalent despite not matching structurally,
    -- like record field extentions with the fields ordered differently.
    -- Those would override the default implementation to handle the unification of mismatching structures.
    structureMismatch ::
        (forall c. Unify m c => UVarOf m # c -> UVarOf m # c -> m (UVarOf m # c)) ->
        t # UVarOf m ->
        t # UVarOf m ->
        m ()
    structureMismatch _ x y = unifyError (Mismatch x y)

    -- TODO: Putting documentation here causes duplication in the haddock documentation
    unifyRecursive :: Proxy m -> RecMethod (Unify m) t
    {-# INLINE unifyRecursive #-}
    default unifyRecursive :: HNodesConstraint t (Unify m) => Proxy m -> RecMethod (Unify m) t
    unifyRecursive _ _ = Dict

instance Recursive (Unify m) where
    {-# INLINE recurse #-}
    recurse = unifyRecursive (Proxy @m) . proxyArgument

-- | A class for unification monads with scope levels
class Unify m t => UnifyGen m t where
    -- | Get the current scope constraint
    scopeConstraints :: Proxy t -> m (TypeConstraintsOf t)

    unifyGenRecursive :: Proxy m -> RecMethod (UnifyGen m) t
    {-# INLINE unifyGenRecursive #-}
    default unifyGenRecursive ::
        HNodesConstraint t (UnifyGen m) => Proxy m -> RecMethod (UnifyGen m) t
    unifyGenRecursive _ _ = Dict

instance Recursive (UnifyGen m) where
    {-# INLINE recurse #-}
    recurse = unifyGenRecursive (Proxy @m) . proxyArgument

-- | Look up a variable, and return last variable pointing to result.
-- Prunes all variables on way to point to the last variable
-- (path-compression ala union-find).
{-# INLINE semiPruneLookup #-}
semiPruneLookup ::
    Unify m t =>
    UVarOf m # t ->
    m (UVarOf m # t, UTerm (UVarOf m) # t)
semiPruneLookup v0 =
    lookupVar binding v0
        >>= \case
            UToVar v1 ->
                do
                    (v, r) <- semiPruneLookup v1
                    bindVar binding v0 (UToVar v)
                    pure (v, r)
            t -> pure (v0, t)

-- | Resolve a term from a unification variable.
--
-- Note that this must be done after
-- all unifications involving the term and its children are done,
-- as it replaces unification state with cached resolved terms.
{-# INLINE applyBindings #-}
applyBindings ::
    forall m t.
    Unify m t =>
    UVarOf m # t ->
    m (Pure # t)
applyBindings v0 =
    semiPruneLookup v0
        >>= \(v1, x) ->
            let result r = r <$ bindVar binding v1 (UResolved r)
                quantify c =
                    newQuantifiedVariable c
                        <&> (_Pure . quantifiedVar #)
                        >>= result
            in  case x of
                    UResolving t -> occursError v1 t
                    UResolved t -> pure t
                    UUnbound c -> quantify c
                    USkolem c -> quantify c
                    UTerm b ->
                        do
                            (r, anyChild) <-
                                htraverse
                                    ( Proxy @(Unify m) #>
                                        \c ->
                                            do
                                                get >>= lift . (`unless` bindVar binding v1 (UResolving b))
                                                put True
                                                applyBindings c & lift
                                    )
                                    (b ^. uBody)
                                    & (`runStateT` False)
                                        \\ unifyRecursive (Proxy @m) (Proxy @t)
                            _Pure # r & if anyChild then result else pure
                    UToVar{} -> error "lookup not expected to result in var"
                    UConverted{} -> error "conversion state not expected in applyBindings"
                    UInstantiated{} ->
                        -- This can happen in alphaEq,
                        -- where UInstantiated marks that var from one side matches var in the other.
                        quantify mempty

-- | Format and throw an occurs check error
occursError ::
    Unify m t =>
    UVarOf m # t ->
    UTermBody (UVarOf m) # t ->
    m a
occursError v (UTermBody c b) =
    do
        q <- newQuantifiedVariable c
        bindVar binding v (UResolved (_Pure . quantifiedVar # q))
        unifyError (Occurs (quantifiedVar # q) b)
