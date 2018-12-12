{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts, LambdaCase, ScopedTypeVariables, TypeFamilies, DefaultSignatures #-}

module AST.Unify
    ( Var, UNode
    , unfreeze
    , Binding(..)
    , MonadOccurs(..)
    , Unify(..)
    , applyBindings, unify
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Recursive (Recursive(..), RecursiveConstraint, wrap)
import           AST.Class.ZipMatch (ZipMatch(..), zipMatch_)
import           AST.Functor.UTerm (UTerm(..))
import           AST.Node (Node)
import           Control.Applicative (Alternative(..))
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Functor.Identity (Identity(..))
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

-- Names modeled after unification-fd

type family Var (m :: * -> *) :: * -> *

type UNode m t = Node (UTerm (Var m)) t
type UVar m t = Var m (t (UTerm (Var m)))

data Binding m t = Binding
    { lookupVar :: UVar m t -> m (Maybe (UNode m t))
    , newVar :: m (UNode m t)
    , bindVar :: UVar m t -> UNode m t -> m ()
    }

class Monad m => MonadOccurs (m :: * -> *) where
    type Visited m
    emptyVisited :: Proxy m -> Visited m

    default emptyVisited :: Monoid (Visited m) => Proxy m -> Visited m
    emptyVisited = mempty

class (Eq (UVar m t), ZipMatch t, MonadOccurs m) => Unify m t where
    binding :: Binding m t

    -- | Add variable to visited set,
    -- or break with an "occurs" failure due to variable resolving to term that contains itself.
    -- For the error, the term is given for context.
    visit :: t (UTerm (Var m)) -> UVar m t -> Visited m -> m (Visited m)

    -- | What to do when top-levels of terms being unified do not match.
    -- Usually this will throw a failure,
    -- but some AST terms could be equivalent despite not matching,
    -- like record extends with fields ordered differently,
    -- and these could still match.
    structureMismatch :: t (UTerm (Var m)) -> t (UTerm (Var m)) -> m ()

    default structureMismatch :: Alternative m => t (UTerm (Var m)) -> t (UTerm (Var m)) -> m ()
    structureMismatch _ _ = empty

-- | Embed a pure term as a mutable term.
unfreeze :: Recursive Children t => Node Identity t -> Node (UTerm v) t
unfreeze = runIdentity . wrap (Proxy :: Proxy Children) (Identity . UTerm)

-- look up a variable, and return last variable pointing to result.
-- prune all variable on way to last variable
semiPruneLookup :: forall m t. Unify m t => UVar m t -> m (UVar m t, Maybe (t (UTerm (Var m))))
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

applyBindings :: forall m t. Recursive (Unify m) t => UNode m t -> m (UNode m t)
applyBindings =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    applyBindingsH (emptyVisited (Proxy :: Proxy m))

applyBindingsH ::
    forall m t.
    Recursive (Unify m) t =>
    Visited m -> UNode m t -> m (UNode m t)
applyBindingsH visited (UTerm t) =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    children (Proxy :: Proxy (Recursive (Unify m))) (applyBindingsH visited) t
    <&> UTerm
applyBindingsH visited (UVar v0) =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    semiPruneLookup v0
    >>=
    \case
    (v1, Nothing) -> UVar v1 & pure
    (v1, Just t) ->
        visit t v1 visited
        >>= (`applyBindingsH` UTerm t)

-- Note on usage of `semiPruneLookup`:
--   Variables are pruned to point to other variables rather than terms,
--   yielding comparison of (sometimes equal) variables,
--   rather than recursively unifying the terms that they would prune to.
unify :: forall m t. Recursive (Unify m) t => UNode m t -> UNode m t -> m ()
unify (UVar v) (UTerm t) = unifyVarTerm v t
unify (UTerm t) (UVar v) = unifyVarTerm v t
unify (UTerm t0) (UTerm t1) = unifyTerms t0 t1
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
        (_, Just x1) -> unifyVarTerm y0 x1
        (x1, Nothing) ->
            semiPruneLookup y0
            >>=
            \case
            (y1, _) | x1 == y1 -> pure ()
            (_, Just y1) -> unifyVarTerm x1 y1
            (y1, Nothing) ->
                bindVar binding x1 (UVar y1)

unifyVarTerm :: forall m t. Recursive (Unify m) t => UVar m t -> t (UTerm (Var m)) -> m ()
unifyVarTerm x0 y =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    semiPruneLookup x0
    >>=
    \case
    (x1, Nothing) -> bindVar binding x1 (UTerm y)
    (_, Just x1) -> unifyTerms x1 y

unifyTerms ::
    forall m t.
    Recursive (Unify m) t =>
    t (UTerm (Var m)) -> t (UTerm (Var m)) -> m ()
unifyTerms x y =
    withDict (recursive :: Dict (RecursiveConstraint t (Unify m))) $
    fromMaybe (structureMismatch x y)
    (zipMatch_ (Proxy :: Proxy (Recursive (Unify m))) unify x y)
