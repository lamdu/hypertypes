{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, MultiParamTypeClasses, FlexibleContexts #-}

module AST.Unify
    ( UTerm(..), _UVar, _UTerm
    , unfreeze, freeze
    , Variable(..)
    , Binding(..)
    , Unify -- not exporting constructor!
    , UnifyMonad(..)
    , unify
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
freeze (UTerm t) = children freeze t <&> Identity

class Eq v => Variable v where
    getVarId :: v -> Int

instance Variable Int where
    getVarId = id

data Binding v t m = Binding
    { lookupVar :: v -> m (t (UTerm v))
    , newVar :: m (Node (UTerm v) t)
    , bindVar :: v -> t (UTerm v) -> m ()
    }

data Unify a = Unify

class (Eq v, MonadError () m) => UnifyMonad v t m where
    binding :: Binding v t m
    unifyBody :: t (UTerm v) -> t (UTerm v) -> m (t Unify)

unify :: UnifyMonad v t m => Node (UTerm v) t -> Node (UTerm v) t -> m (Node Unify t)
unify x0 x1 =
    Unify <$
    case (x0, x1, Proxy) of
    (UVar v, UTerm t, _) -> bindVar binding v t
    (UTerm t, UVar v, _) -> bindVar binding v t
    (UTerm t0, UTerm t1, p) -> unifyBody (t0 `asProxyTypeOf` p) t1 & void
    (UVar v0, UVar v1, p)
        | v0 == v1 -> pure ()
        | otherwise ->
            unifyBody
            <$> (lookupVar binding v0 <&> (`asProxyTypeOf` p))
            <*> lookupVar binding v1
            & join & void
