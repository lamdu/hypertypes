{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, LambdaCase #-}

module AST.Unify
    ( UTerm(..), _UVar, _UTerm
    , unfreeze, freeze
    , Variable(..)
    , Binding(..)
    , Unify -- not exporting constructor!
    , UnifyMonad(..)
    , applyBindings, unify
    ) where

import           AST
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad
import           Control.Monad.Except (MonadError(..))
import           Control.Monad.Trans.State
import           Data.Functor.Identity (Identity(..))
import           Data.IntMap (IntMap)
import           Data.Maybe (fromMaybe)
import           Data.Proxy

import           Prelude.Compat

-- Names modeled after unification-fd

data UTerm v t
    = UVar v
    | UTerm t
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makePrisms ''UTerm

-- | Embed a pure term as a mutable term.
unfreeze :: Children t => Node Identity t -> Node (UTerm v) t
unfreeze (Identity t) = overChildren unfreeze t & UTerm

freeze :: Children t => Node (UTerm v) t -> Maybe (Node Identity t)
freeze UVar{} = Nothing
freeze (UTerm t) = traverseChildren freeze t <&> Identity

class Eq v => Variable v where
    getVarId :: v -> Int

instance Variable Int where
    getVarId = id

data Binding v t m = Binding
    { lookupVar :: v -> m (Maybe (Node (UTerm v) t))
    , newVar :: m (Node (UTerm v) t)
    , bindVar :: v -> Node (UTerm v) t -> m ()
    }

data Unify a = Unify

class (Eq v, Children t, MonadError () m) => UnifyMonad v t m where
    binding :: Binding v t m
    applyBindingsBody :: t (UTerm v) -> m (t (UTerm v))
    unifyBody :: t (UTerm v) -> t (UTerm v) -> m (t Unify)

applyBindings :: UnifyMonad v t m => Node (UTerm v) t -> m (Node (UTerm v) t)
applyBindings (UTerm t) = applyBindingsBody t <&> UTerm
applyBindings (UVar v) =
    lookupVar binding v
    >>=
    \case
    Nothing -> pure (UVar v)
    Just v1@UVar{} -> pure v1
    Just (UTerm t) -> applyBindingsBody t <&> UTerm

unify :: UnifyMonad v t m => Node (UTerm v) t -> Node (UTerm v) t -> m (Node Unify t)
unify x0 x1 =
    Unify <$
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
