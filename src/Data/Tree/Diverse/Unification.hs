{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, RankNTypes #-}

module Data.Tree.Diverse.Unification
    where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad
import           Control.Monad.Except (MonadError(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy
import           Data.Tree.Diverse

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

class (Variable v, MonadError () m) => UnifyMonad v t m where
    bindVar :: v -> t (UTerm v) -> m ()
    lookupVar :: v -> m (t (UTerm v))
    unifyBody :: t (UTerm v) -> t (UTerm v) -> m ()

unify :: UnifyMonad v t m => Node (UTerm v) t -> Node (UTerm v) t -> m ()
unify x0 x1 =
    case (x0, x1, Proxy) of
    (UVar v, UTerm t, _) -> bindVar v t
    (UTerm t, UVar v, _) -> bindVar v t
    (UTerm t0, UTerm t1, p) -> unifyBody (t0 `asProxyTypeOf` p) t1
    (UVar v0, UVar v1, p)
        | v0 == v1 -> pure ()
        | otherwise ->
            unifyBody
            <$> (lookupVar v0 <&> (`asProxyTypeOf` p))
            <*> lookupVar v1
            & join
