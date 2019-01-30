{-# LANGUAGE NoImplicitPrelude #-}

module AST.Infer
    ( module AST.Class.Infer
    , module AST.Infer.Inferred
    , module AST.Infer.ScopeLevel
    , module AST.Infer.Term
    , inferNode
    ) where

import AST
import AST.Class.Infer
import AST.Infer.Inferred
import AST.Infer.ScopeLevel
import AST.Infer.Term
import AST.Unify

import Prelude.Compat

{-# INLINE inferNode #-}
inferNode :: Infer m t => Tree (Ann a) t -> m (Tree (ITerm a (UVar m)) t)
inferNode (Ann a x) =
    (\s (t, xI) -> ITerm xI t s a)
    <$> getScope
    <*> infer x
