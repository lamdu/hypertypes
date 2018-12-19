{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts, LambdaCase, ScopedTypeVariables, TypeFamilies, DefaultSignatures, DataKinds #-}

module AST.Unify
    ( HasQuantifiedVar(..)
    , UniVar
    , unfreeze
    , Binding(..)
    , Unify(..)
    , applyBindings, unify
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Recursive (Recursive(..), RecursiveConstraint, wrap)
import           AST.Class.ZipMatch (ZipMatch(..), zipMatchWith_)
import           AST.Knot.Pure (Pure(..))
import           AST.Knot (Knot, Tree)
import           AST.Unify.Term
import           Control.Applicative (Alternative(..))
import           Control.Lens.Operators
import           Data.Constraint (Dict, withDict)
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

class HasQuantifiedVar (t :: Knot -> *) where
    type family QVar t
    quantifiedVar :: QVar t -> t f

-- Names modeled after unification-fd

-- Unification variable type for a unification monad
type family UniVar (m :: * -> *) :: Knot -> *

data Binding m t = Binding
    { lookupVar :: Tree (UniVar m) t -> m (Maybe (Tree (VTerm (UniVar m)) t))
    , newVar :: m (Tree (UTerm (UniVar m)) t)
    , bindVar :: Tree (UniVar m) t -> Tree (VTerm (UniVar m)) t -> m ()
    }

class (Eq (Tree (UniVar m) t), ZipMatch t, HasQuantifiedVar t, Monad m) => Unify m t where
    binding :: Binding m t

    newQuantifiedVariable :: Proxy t -> m (QVar t)
    -- Default for type languages which force quantified variables to a specific type or a hole type
    default newQuantifiedVariable :: QVar t ~ () => Proxy t -> m (QVar t)
    newQuantifiedVariable _ = pure ()

    -- | A unification variable was unified with a type that contains itself,
    -- therefore the type is infinite.
    -- Break with an error if the type system doesn't allow it,
    -- or resolve the situation and generate the type represeting this loop.
    occurs :: Tree (UniVar m) t -> Tree t (UTerm (UniVar m)) -> m (Tree Pure t)
    default occurs :: Alternative m => Tree (UniVar m) t -> Tree t (UTerm (UniVar m)) -> m (Tree Pure t)
    occurs _ _ = empty

    -- | What to do when top-levels of terms being unified do not match.
    -- Usually this will throw a failure,
    -- but some AST terms could be equivalent despite not matching,
    -- like record extends with fields ordered differently,
    -- and these could still match.
    structureMismatch :: Tree t (UTerm (UniVar m)) -> Tree t (UTerm (UniVar m)) -> m ()
    default structureMismatch ::
        Alternative m => Tree t (UTerm (UniVar m)) -> Tree t (UTerm (UniVar m)) -> m ()
    structureMismatch _ _ = empty

-- | Embed a pure term as a mutable term.
unfreeze :: Recursive Children t => Tree Pure t -> Tree (UTerm v) t
unfreeze = wrap (Proxy :: Proxy Children) UTerm

-- look up a variable, and return last variable pointing to result.
-- prune all variable on way to last variable
semiPruneLookup ::
    forall m t.
    Unify m t =>
    Tree (UniVar m) t ->
    m (Tree (UniVar m) t, Tree (VTerm (UniVar m)) t)
semiPruneLookup v0 =
    lookupVar binding v0
    >>=
    \case
    Nothing -> pure (v0, VVar v0)
    Just (VVar v1) ->
        do
            (v, r) <- semiPruneLookup v1
            bindVar binding v0 (VVar v)
            pure (v, r)
    Just t -> pure (v0, t)

-- TODO: implement when need / better understand motivations for -
-- freeze, fullPrune, occursIn, seenAs, getFreeVars, freshen, equals, equiv

applyBindings :: forall m t. Recursive (Unify m) t => Tree (UTerm (UniVar m)) t -> m (Tree Pure t)
applyBindings (UTerm t) =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    children (Proxy :: Proxy (Recursive (Unify m))) applyBindings t
    <&> Pure
applyBindings (UVar v0) =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    semiPruneLookup v0
    >>=
    \case
    (_, VResolved t) -> pure t
    (v1, VVar{}) ->
        do
            qvar <- newQuantifiedVariable (Proxy :: Proxy t)
            bindVar binding v1 (VTerm (quantifiedVar qvar))
            quantifiedVar qvar & Pure & pure
    (v1, VResolving t) -> occurs v1 t
    (v1, VTerm t) ->
        case leafExpr of
        Just f -> f t & Pure & pure
        Nothing ->
            do
                bindVar binding v1 (VResolving t)
                r <- applyBindings (UTerm t)
                bindVar binding v1 (VResolved r)
                pure r

-- Note on usage of `semiPruneLookup`:
--   Variables are pruned to point to other variables rather than terms,
--   yielding comparison of (sometimes equal) variables,
--   rather than recursively unifying the terms that they would prune to.
unify ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UTerm (UniVar m)) t ->
    Tree (UTerm (UniVar m)) t ->
    m ()
unify (UVar v) (UTerm t) = unifyVarTerm v t
unify (UTerm t) (UVar v) = unifyVarTerm v t
unify (UTerm t0) (UTerm t1) = unifyTerms t0 t1
unify (UVar x) (UVar y) = withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) (unifyVars x y)

unifyVars ::
    (Recursive (Unify m) t, RecursiveConstraint t (Unify m)) =>
    Tree (UniVar m) t -> Tree (UniVar m) t -> m ()
unifyVars x0 y0
    | x0 == y0 = pure ()
    | otherwise =
        semiPruneLookup x0
        >>=
        \case
        (x1, _) | x1 == y0 -> pure ()
        (_, VTerm x1) -> unifyVarTerm y0 x1
        (x1, VVar{}) ->
            semiPruneLookup y0
            >>=
            \case
            (y1, _) | x1 == y1 -> pure ()
            (_, VTerm y1) -> unifyVarTerm x1 y1
            (y1, VVar{}) ->
                bindVar binding x1 (VVar y1)
            (_, _) -> error "This shouldn't happen in unification stage"
        (_, _) -> error "This shouldn't happen in unification stage"

unifyVarTerm ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UniVar m) t -> Tree t (UTerm (UniVar m)) -> m ()
unifyVarTerm x0 y =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    semiPruneLookup x0
    >>=
    \case
    (x1, VVar{}) -> bindVar binding x1 (VTerm y)
    (_, VTerm x1) -> unifyTerms x1 y
    (_, _) -> error "This shouldn't happen in unification stage"

unifyTerms ::
    forall m t.
    Recursive (Unify m) t =>
    Tree t (UTerm (UniVar m)) ->
    Tree t (UTerm (UniVar m)) ->
    m ()
unifyTerms x y =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    fromMaybe (structureMismatch x y)
    (zipMatchWith_ (Proxy :: Proxy (Recursive (Unify m))) unify x y)
