{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, LambdaCase, ScopedTypeVariables, UndecidableInstances, UndecidableSuperClasses, TypeFamilies, DefaultSignatures #-}

module AST.Unify
    ( UTerm(..), _UVar, _UTerm
    , unfreeze
    , Binding(..)
    , OccursMonad(..)
    , UnifyMonad(..)
    , applyBindings, unify
    ) where

import           AST (Node, Children(..), overChildren)
import           AST.ZipMatch (ZipMatch(..), zipMatch_)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Except (MonadError(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

-- Names modeled after unification-fd

data UTerm v t
    = UVar v
    | UTerm t
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makePrisms ''UTerm

-- | Embed a pure term as a mutable term.
unfreeze :: Children t => Node Identity t -> Node (UTerm v) t
unfreeze (Identity t) = overChildren (Proxy :: Proxy Children) unfreeze t & UTerm

data Binding v t m = Binding
    { lookupVar :: v -> m (Maybe (Node (UTerm v) t))
    , newVar :: m (Node (UTerm v) t)
    , bindVar :: v -> Node (UTerm v) t -> m ()
    }

class MonadError () m => OccursMonad m where
    type Visited m
    emptyVisited :: Proxy m -> Visited m

    default emptyVisited :: Monoid (Visited m) => Proxy m -> Visited m
    emptyVisited = mempty

class
    ( Eq v, ZipMatch t, OccursMonad m
    , ChildrenConstraint t (UnifyMonad m v)
    ) => UnifyMonad m v t where
    binding :: Binding v t m
    visit :: Proxy t -> v -> Visited m -> m (Visited m)

-- look up a variable, and return last variable pointing to result.
-- prune all variable on way to last variable
semiPruneLookup :: UnifyMonad m v t => v -> m (v, Maybe (t (UTerm v)))
semiPruneLookup v0 =
    lookupVar binding v0
    >>=
    \case
    Nothing -> pure (v0, Nothing)
    Just (UTerm t) -> pure (v0, Just t)
    Just u@(UVar v1) ->
        do
            (v, r) <- semiPruneLookup v1
            bindVar binding v0 (UVar v `asTypeOf` u)
            pure (v, r)

-- TODO: implement when need / better understand motivations for -
-- freeze, fullPrune, occursIn, seenAs, getFreeVars, freshen, equals, equiv

applyBindings :: forall m v t. UnifyMonad m v t => Node (UTerm v) t -> m (Node (UTerm v) t)
applyBindings = applyBindingsH (emptyVisited (Proxy :: Proxy m))

applyBindingsH ::
    forall m v t.
    UnifyMonad m v t =>
    Visited m -> Node (UTerm v) t -> m (Node (UTerm v) t)
applyBindingsH visited (UTerm t) =
    children (Proxy :: Proxy (UnifyMonad m v)) (applyBindingsH visited) t <&> UTerm
applyBindingsH visited (UVar v0) =
    semiPruneLookup v0
    >>=
    \case
    (v1, Nothing) -> UVar v1 & pure
    (v1, Just t) ->
        visit (Proxy :: Proxy t) v1 visited
        >>= (`applyBindingsH` UTerm t)

-- Note on usage of `semiPruneLookup`:
--   Variables are pruned to point to other variables rather than terms,
--   yielding comparison of (sometimes equal) variables,
--   rather than recursively unifying the terms they would prune to.
unify :: forall m v t. UnifyMonad m v t => Node (UTerm v) t -> Node (UTerm v) t -> m ()
unify (UVar v) (UTerm t) = unifyVarTerm v t
unify (UTerm t) (UVar v) = unifyVarTerm v t
unify (UTerm t0) (UTerm t1) = unifyTerms t0 t1
unify (UVar x0) (UVar y0)
    | x0 == y0 = pure ()
    | otherwise =
        semiPruneLookup x0
        >>=
        \case
        (_, Just x1) -> unifyVarTerm y0 (x1 :: t (UTerm v))
        (x1, Nothing) ->
            semiPruneLookup y0
            >>=
            \case
            (_, Just y1) -> unifyVarTerm x1 (y1 :: t (UTerm v))
            (y1, Nothing) ->
                bindVar binding x1 (UVar y1 :: Node (UTerm v) t)

unifyVarTerm :: UnifyMonad m v t => v -> t (UTerm v) -> m ()
unifyVarTerm x0 y =
    semiPruneLookup x0
    >>=
    \case
    (x1, Nothing) -> bindVar binding x1 (UTerm y)
    (_, Just x1) -> unifyTerms x1 y

unifyTerms ::
    forall m v t. UnifyMonad m v t =>
    t (UTerm v) -> t (UTerm v) -> m ()
unifyTerms =
    zipMatch_ (Proxy :: Proxy (UnifyMonad m v)) unify
