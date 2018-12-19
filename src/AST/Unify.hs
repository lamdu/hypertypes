{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts, LambdaCase, ScopedTypeVariables, TypeFamilies, DefaultSignatures, DataKinds #-}

module AST.Unify
    ( HasQuantifiedVar(..)
    , UniVar
    , Binding(..)
    , Unify(..)
    , applyBindings, unify
    ) where

import AST.Class.Children (Children(..))
import AST.Class.Recursive (Recursive(..), RecursiveDict)
import AST.Class.ZipMatch (ZipMatch(..), zipMatchWithA)
import AST.Knot.Pure (Pure(..))
import AST.Knot (Knot, Tree)
import AST.Unify.Term
import Control.Applicative (Alternative(..))
import Control.Lens (Prism')
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class Ord (QVar t) => HasQuantifiedVar (t :: Knot -> *) where
    type family QVar t
    quantifiedVar :: Prism' (t f) (QVar t)

-- Names modeled after unification-fd

-- Unification variable type for a unification monad
type family UniVar (m :: * -> *) :: Knot -> *

data Binding m t = Binding
    { lookupVar :: Tree (UniVar m) t -> m (Tree (UTerm (UniVar m)) t)
    , newVar :: Tree (UTerm (UniVar m)) t -> m (Tree (UniVar m) t)
    , bindVar :: Tree (UniVar m) t -> Tree (UTerm (UniVar m)) t -> m ()
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
    occurs :: Tree (UniVar m) t -> Tree t (UniVar m) -> m (Tree Pure t)
    default occurs :: Alternative m => Tree (UniVar m) t -> Tree t (UniVar m) -> m (Tree Pure t)
    occurs _ _ = empty

    -- | What to do when top-levels of terms being unified do not match.
    -- Usually this will throw a failure,
    -- but some AST terms could be equivalent despite not matching,
    -- like record extends with fields ordered differently,
    -- and these could still match.
    structureMismatch :: Tree (UTermBody (UniVar m)) t -> Tree (UTermBody (UniVar m)) t -> m (Tree t (UniVar m))
    default structureMismatch ::
        Alternative m => Tree (UTermBody (UniVar m)) t -> Tree (UTermBody (UniVar m)) t -> m (Tree t (UniVar m))
    structureMismatch _ _ = empty

    skolemUnified :: Tree (UniVar m) t -> Tree (UniVar m) t -> m ()
    default skolemUnified :: Alternative m => Tree (UniVar m) t -> Tree (UniVar m) t -> m ()
    skolemUnified _ _ = empty

    skolemEscape :: Tree (UniVar m) t -> m ()
    default skolemEscape :: Alternative m => Tree (UniVar m) t -> m ()
    skolemEscape _ = empty

-- look up a variable, and return last variable pointing to result.
-- prune all variable on way to last variable
semiPruneLookup ::
    forall m t.
    Unify m t =>
    Tree (UniVar m) t ->
    m (Tree (UniVar m) t, Tree (UTerm (UniVar m)) t)
semiPruneLookup v0 =
    lookupVar binding v0
    >>=
    \case
    UVar v1 ->
        do
            (v, r) <- semiPruneLookup v1
            bindVar binding v0 (UVar v)
            pure (v, r)
    t -> pure (v0, t)

-- TODO: implement when need / better understand motivations for -
-- freeze, fullPrune, occursIn, seenAs, getFreeVars, freshen, equals, equiv

applyBindings :: forall m t. Recursive (Unify m) t => Tree (UniVar m) t -> m (Tree Pure t)
applyBindings v0 =
    withDict (recursive :: RecursiveDict (Unify m) t) $
    semiPruneLookup v0
    >>=
    \(v1, x) ->
    let result r = r <$ bindVar binding v1 (UResolved r)
        quantify =
            newQuantifiedVariable (Proxy :: Proxy t) <&> (quantifiedVar #) <&> Pure
            >>= result
    in
    case x of
    UResolving t -> occurs v1 t
    UResolved t -> pure t
    UUnbound{} -> quantify
    USkolem{} -> quantify
    UTerm UTermBody{_uBody = t} ->
        case leafExpr of
        Just f -> f t & Pure & pure
        Nothing ->
            do
                bindVar binding v1 (UResolving t)
                children (Proxy :: Proxy (Recursive (Unify m))) applyBindings t
            <&> Pure
            >>= result
    UVar{} -> error "lookup not expected to result in var"

updateLevel ::
    forall m t.
    Recursive (Unify m) t =>
    InferLevel -> Tree (UniVar m) t -> m (Tree (UniVar m) t)
updateLevel level var =
    withDict (recursive :: RecursiveDict (Unify m) t) $
    do
        (v1, x) <- semiPruneLookup var
        case x of
            UUnbound l
                | l <= level -> pure ()
                | otherwise -> bindVar binding v1 (UUnbound level)
            USkolem l
                | l <= level -> pure ()
                | otherwise -> skolemEscape v1
            UTerm t -> updateTermLevel v1 t level
            UResolving t -> () <$ occurs var t
            _ -> error "This shouldn't happen in unification stage"
        pure v1

updateTermLevel ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UniVar m) t -> Tree (UTermBody (UniVar m)) t -> InferLevel -> m ()
updateTermLevel v t level =
    withDict (recursive :: RecursiveDict (Unify m) t) $
    if level >= t ^. uLevel
        then pure ()
        else
            do
                bindVar binding v (UResolving (t ^. uBody))
                children (Proxy :: Proxy (Recursive (Unify m))) (updateLevel level) (t ^. uBody)
                    >>= bindVar binding v . UTerm . UTermBody level

-- Note on usage of `semiPruneLookup`:
--   Variables are pruned to point to other variables rather than terms,
--   yielding comparison of (sometimes equal) variables,
--   rather than recursively unifying the terms that they would prune to.
unify ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UniVar m) t -> Tree (UniVar m) t -> m (Tree (UniVar m) t)
unify x0 y0 =
    withDict (recursive :: RecursiveDict (Unify m) t) $
    let unifyTerms x1 xt y1 yt =
            do
                bindVar binding y1 (UVar x1)
                zipMatchWithA (Proxy :: Proxy (Recursive (Unify m))) unify (xt ^. uBody) (yt ^. uBody)
                    & fromMaybe (structureMismatch xt yt)
                    >>= bindVar binding x1 . UTerm . UTermBody (min (xt ^. uLevel) (yt ^. uLevel))
                pure x1
    in
    if x0 == y0
        then pure x0
        else go x0 y0 (unbound y0) (\x1 xt -> go y0 x1 (bindToTerm x1 xt) (unifyTerms x1 xt))
    where
        bindToTerm dstVar dstTerm var level =
            do
                bindVar binding var (UVar dstVar)
                updateTermLevel dstVar dstTerm level
                pure dstVar
        unbound other var level =
            do
                r <- updateLevel level other
                r <$ bindVar binding var (UVar r)
        go var other onUnbound onTerm =
            semiPruneLookup var
            >>=
            \case
            (v1, _) | v1 == other -> pure other
            (v1, USkolem{}) -> other <$ skolemUnified v1 other
            (v1, UUnbound level) -> onUnbound v1 level
            (v1, UTerm t) -> onTerm v1 t
            (_, _) -> error "This shouldn't happen in unification stage"
