{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, FlexibleContexts #-}

module AST.Infer
    ( module AST.Class.Infer
    , module AST.Infer.ScopeLevel
    , module AST.Infer.Term
    , infer
    ) where

import AST
import AST.Class.Infer
import AST.Class.Recursive (recursiveOverChildren)
import AST.Infer.ScopeLevel
import AST.Infer.Term
import AST.Unify (UVarOf)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

{-# INLINE infer #-}
infer ::
    forall m t a.
    Recursive (Infer m) t =>
    Tree (Ann a) t -> m (Tree (ITerm a (UVarOf m)) t)
infer (Ann a x) =
    (\s (t, xI) -> ITerm a (IResult t s) xI)
    <$> getScope
    <*> inferBody
        (recursiveOverChildren (Proxy :: Proxy (Infer m))
            (\c -> infer c <&> (\i -> (i ^. iType, i)) & InferIn)
            x)
