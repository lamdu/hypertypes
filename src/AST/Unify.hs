{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, LambdaCase, ScopedTypeVariables, UndecidableInstances, UndecidableSuperClasses, TypeFamilies, DefaultSignatures #-}

module AST.Unify
    ( UTerm(..), _UVar, _UTerm
    , unfreeze, freeze
    , Binding(..)
    , OccursMonad(..)
    , UnifyMonad(..)
    , applyBindings, unify
    ) where

import           AST (Node, Children(..), overChildren)
import           AST.ZipMatch (ZipMatch(..), zipMatch_)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (void)
import           Control.Monad.Except (MonadError(..))
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Reader
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..), asProxyTypeOf)

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

freeze :: Children t => Node (UTerm v) t -> Maybe (Node Identity t)
freeze UVar{} = Nothing
freeze (UTerm t) = children (Proxy :: Proxy Children) freeze t <&> Identity

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

-- TODO: What is fullPrune used for in unification-fd?
_fullPrune :: UnifyMonad m v t => Node (UTerm v) t -> m (Node (UTerm v) t)
_fullPrune (UTerm t) = UTerm t & pure
_fullPrune (UVar v) =
    lookupVar binding v
    >>= Lens._Just _fullPrune
    >>=
    \case
    Nothing -> UVar v & pure
    Just r -> r <$ bindVar binding v r

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

-- TODO: implement when better understand motivations for -
-- occursIn, seenAs, getFreeVars

applyBindings :: forall m v t. UnifyMonad m v t => Node (UTerm v) t -> m (Node (UTerm v) t)
applyBindings x =
    runReaderT (applyBindingsH x) (emptyVisited (Proxy :: Proxy m))

applyBindingsH ::
    forall m v t.
    UnifyMonad m v t =>
    Node (UTerm v) t -> ReaderT (Visited m) m (Node (UTerm v) t)
applyBindingsH (UTerm t) =
    children (Proxy :: Proxy (UnifyMonad m v)) applyBindingsH t <&> UTerm
applyBindingsH (UVar v0) =
    semiPruneLookup v0 & lift
    >>=
    \case
    (v1, Nothing) -> UVar v1 & pure
    (v1, Just t) ->
        do
            newVisit <- ask >>= lift . visit (Proxy :: Proxy t) v1
            local (const newVisit) (applyBindingsH (UTerm t))

unify :: UnifyMonad m v t => Node (UTerm v) t -> Node (UTerm v) t -> m ()
unify x0 x1 =
    case (x0, x1, Proxy) of
    (UVar v, t@UTerm{}, p) -> bindVar binding v (t `asProxyTypeOf` p)
    (t@UTerm{}, UVar v, _) -> bindVar binding v t
    (UTerm t0, UTerm t1, _) -> unifyBody t0 t1 & void
    (UVar v0, UVar v1, p)
        | v0 == v1 -> pure ()
        | otherwise ->
            lookupVar binding v0
            >>=
            \case
            Nothing -> bindVar binding v0 (UVar v1 `asProxyTypeOf` p)
            Just t0 ->
                lookupVar binding v1
                >>=
                \case
                Nothing -> bindVar binding v1 (UVar v0 `asProxyTypeOf` p)
                Just t1 -> unify (t0 `asProxyTypeOf` p) t1 & void

unifyBody :: forall m v t. UnifyMonad m v t => t (UTerm v) -> t (UTerm v) -> m ()
unifyBody = zipMatch_ (Proxy :: Proxy (UnifyMonad m v)) unify
