{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, LambdaCase, ScopedTypeVariables, UndecidableInstances, UndecidableSuperClasses #-}

module AST.Unify
    ( UTerm(..), _UVar, _UTerm
    , unfreeze, freeze
    , Binding(..)
    , UnifyMonad(..)
    , applyBindings, unify
    ) where

import           AST (Node, Children(..), overChildren)
import           AST.ZipMatch (ZipMatch(..), zipMatch_)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (void)
import           Control.Monad.Except (MonadError(..))
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

class
    ( Eq v, ZipMatch t, MonadError () m
    , ChildrenConstraint t (UnifyMonad m v)
    ) =>
    UnifyMonad m v t where
    binding :: Binding v t m

fullPrune :: UnifyMonad m v t => Node (UTerm v) t -> m (Node (UTerm v) t)
fullPrune (UTerm t) = UTerm t & pure
fullPrune (UVar v) =
    lookupVar binding v
    >>= Lens._Just fullPrune
    >>=
    \case
    Nothing -> UVar v & pure
    Just r -> r <$ bindVar binding v r

-- TODO: implement when better understand motivations for -
-- semiprune, occursIn, seenAs, getFreeVars

applyBindings :: UnifyMonad m v t => Node (UTerm v) t -> m (Node (UTerm v) t)
applyBindings x =
    fullPrune x -- TODO: unification-fd uses semiprune
    >>=
    \case
    UVar v -> UVar v & pure
    UTerm t -> applyBindingsBody t <&> UTerm
    where
        -- TODO: occurs check
        applyBindingsBody :: forall m v t. UnifyMonad m v t => t (UTerm v) -> m (t (UTerm v))
        applyBindingsBody = children (Proxy :: Proxy (UnifyMonad m v)) applyBindings

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
