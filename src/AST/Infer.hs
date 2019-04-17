{-# LANGUAGE NoImplicitPrelude #-}

module AST.Infer
    ( module AST.Class.Infer
    , module AST.Infer.ScopeLevel
    , module AST.Infer.Term
    , infer
    ) where

import AST
import AST.Class.Infer
import AST.Infer.ScopeLevel
import AST.Infer.Term
import AST.Unify

import Prelude.Compat

{-# INLINE infer #-}
infer :: Infer m t => Tree (Ann a) t -> m (Tree (ITerm a (UVarOf m)) t)
infer (Ann a x) =
    (\s (t, xI) -> ITerm a (IResult t s) xI)
    <$> getScope
    <*> inferBody x
