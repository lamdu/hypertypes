{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts, LambdaCase, ScopedTypeVariables, TypeFamilies, DefaultSignatures #-}

module AST.Unify
    ( HasQuantifiedVar(..)
    , UniVar, UNode
    , unfreeze
    , Binding(..)
    , Unify(..)
    , applyBindings, unify
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Recursive (Recursive(..), RecursiveConstraint, wrap)
import           AST.Class.ZipMatch (ZipMatch(..), zipMatch_)
import           AST.Knot.UTerm
import           AST.Node (Node)
import           Control.Applicative (Alternative(..))
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Functor.Identity (Identity(..))
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

class HasQuantifiedVar (t :: (* -> *) -> *) where
    type family QVar t
    quantifiedVar :: QVar t -> t f

-- Names modeled after unification-fd

-- Unification variable type for a unification monad
type family UniVar (m :: * -> *) :: * -> *

type UNode m t = Node (UTerm (UniVar m)) t
type UVar m t = UniVar m (t (UTerm (UniVar m)))

data Binding m t = Binding
    { lookupVar :: UVar m t -> m (Maybe (UNode m t))
    , newVar :: m (UNode m t)
    , bindVar :: UVar m t -> UNode m t -> m ()
    }

class (Eq (UVar m t), ZipMatch t, HasQuantifiedVar t, Monad m) => Unify m t where
    binding :: Binding m t

    newQuantifiedVariable :: Proxy t -> m (QVar t)
    -- Default for type languages which force quantified variables to a specific type or a hole type
    default newQuantifiedVariable :: QVar t ~ () => Proxy t -> m (QVar t)
    newQuantifiedVariable _ = pure ()

    -- | A unification variable was unified with a type that contains itself,
    -- therefore the type is infinite.
    -- Break with an error if the type system doesn't allow it,
    -- or resolve the situation and generate the type represeting this loop.
    occurs :: UVar m t -> t (UTerm (UniVar m)) -> m (Node Identity t)
    default occurs :: Alternative m => UVar m t -> t (UTerm (UniVar m)) -> m (Node Identity t)
    occurs _ _ = empty

    -- | What to do when top-levels of terms being unified do not match.
    -- Usually this will throw a failure,
    -- but some AST terms could be equivalent despite not matching,
    -- like record extends with fields ordered differently,
    -- and these could still match.
    structureMismatch :: t (UTerm (UniVar m)) -> t (UTerm (UniVar m)) -> m ()
    default structureMismatch :: Alternative m => t (UTerm (UniVar m)) -> t (UTerm (UniVar m)) -> m ()
    structureMismatch _ _ = empty

-- | Embed a pure term as a mutable term.
unfreeze :: Recursive Children t => Node Identity t -> Node (UTerm v) t
unfreeze = wrap (Proxy :: Proxy Children) newUTerm

-- look up a variable, and return last variable pointing to result.
-- prune all variable on way to last variable
semiPruneLookup :: forall m t. Unify m t => UVar m t -> m (UVar m t, Maybe (UBody (t (UTerm (UniVar m)))))
semiPruneLookup v0 =
    lookupVar binding v0
    >>=
    \case
    Nothing -> pure (v0, Nothing)
    Just (UTerm t) -> pure (v0, Just t)
    Just (UVar v1) ->
        do
            (v, r) <- semiPruneLookup v1
            bindVar binding v0 (UVar v)
            pure (v, r)

-- TODO: implement when need / better understand motivations for -
-- freeze, fullPrune, occursIn, seenAs, getFreeVars, freshen, equals, equiv

applyBindings :: forall m t. Recursive (Unify m) t => UNode m t -> m (Node Identity t)
applyBindings (UTerm t) =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    children (Proxy :: Proxy (Recursive (Unify m))) applyBindings (t ^. uBody)
    <&> Identity
applyBindings (UVar v0) =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    semiPruneLookup v0
    >>=
    \case
    (v1, Nothing) ->
        do
            qvar <- newQuantifiedVariable (Proxy :: Proxy t)
            bindVar binding v1 (newUTerm (quantifiedVar qvar))
            quantifiedVar qvar & Identity & pure
    (v1, Just t) ->
        case leafExpr of
        Just f -> t ^. uBody & f & Identity & pure
        Nothing
            | t ^. uVisited -> occurs v1 (t ^. uBody)
            | otherwise ->
                do
                    t & uVisited .~ True & UTerm & bindVar binding v1
                    r <- applyBindings (UTerm t)
                    bindVar binding v1 (UTerm t)
                    pure r

-- Note on usage of `semiPruneLookup`:
--   Variables are pruned to point to other variables rather than terms,
--   yielding comparison of (sometimes equal) variables,
--   rather than recursively unifying the terms that they would prune to.
unify :: forall m t. Recursive (Unify m) t => UNode m t -> UNode m t -> m ()
unify (UVar v) (UTerm t) = unifyVarTerm v (t ^. uBody)
unify (UTerm t) (UVar v) = unifyVarTerm v (t ^. uBody)
unify (UTerm t0) (UTerm t1) = unifyTerms (t0 ^. uBody) (t1 ^. uBody)
unify (UVar x) (UVar y) = withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) (unifyVars x y)

unifyVars ::
    (Recursive (Unify m) t, RecursiveConstraint t (Unify m)) =>
    UVar m t -> UVar m t -> m ()
unifyVars x0 y0
    | x0 == y0 = pure ()
    | otherwise =
        semiPruneLookup x0
        >>=
        \case
        (x1, _) | x1 == y0 -> pure ()
        (_, Just x1) -> unifyVarTerm y0 (x1 ^. uBody)
        (x1, Nothing) ->
            semiPruneLookup y0
            >>=
            \case
            (y1, _) | x1 == y1 -> pure ()
            (_, Just y1) -> unifyVarTerm x1 (y1 ^. uBody)
            (y1, Nothing) ->
                bindVar binding x1 (UVar y1)

unifyVarTerm :: forall m t. Recursive (Unify m) t => UVar m t -> t (UTerm (UniVar m)) -> m ()
unifyVarTerm x0 y =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    semiPruneLookup x0
    >>=
    \case
    (x1, Nothing) -> bindVar binding x1 (newUTerm y)
    (_, Just x1) -> unifyTerms (x1 ^. uBody) y

unifyTerms ::
    forall m t.
    Recursive (Unify m) t =>
    t (UTerm (UniVar m)) -> t (UTerm (UniVar m)) -> m ()
unifyTerms x y =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    fromMaybe (structureMismatch x y)
    (zipMatch_ (Proxy :: Proxy (Recursive (Unify m))) unify x y)
