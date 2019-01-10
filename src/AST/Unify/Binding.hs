{-# LANGUAGE NoImplicitPrelude #-}

module AST.Unify.Binding
    ( Binding(..)
    ) where

import AST.Knot (Tree)
import AST.Unify.Term (UTerm)

data Binding v m t = Binding
    { lookupVar :: Tree v t -> m (Tree (UTerm v) t)
    , newVar :: Tree (UTerm v) t -> m (Tree v t)
    , bindVar :: Tree v t -> Tree (UTerm v) t -> m ()
    }
