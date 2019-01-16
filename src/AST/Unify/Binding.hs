{-# LANGUAGE NoImplicitPrelude #-}

module AST.Unify.Binding
    ( Binding(..)
    ) where

import AST.Knot (Tree)
import AST.Unify.Term (UTerm)

-- | Binding, parameterized on:
--
-- * `v`: unification variable type
-- * `m`: monad to bind in
-- * `t`: term type
--
-- Has 2 implementations in syntax-tree:
--
-- * "AST.Unify.Binding.Pure"
-- * "AST.Unify.Binding.ST"
data Binding v m t = Binding
    { lookupVar :: Tree v t -> m (Tree (UTerm v) t)
    , newVar :: Tree (UTerm v) t -> m (Tree v t)
    , bindVar :: Tree v t -> Tree (UTerm v) t -> m ()
    }
