{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, FlexibleContexts, DataKinds #-}

module AST.Infer
    ( module AST.Class.Infer
    , module AST.Infer.Result
    , module AST.Infer.ScopeLevel
    , module AST.Infer.Term
    , infer
    ) where

import AST
import AST.Class.Infer
import AST.Infer.Result
import AST.Infer.ScopeLevel
import AST.Infer.Term
import AST.Unify (UVarOf)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

import Prelude.Compat

{-# INLINE infer #-}
infer ::
    forall m t a.
    (Recursively (Infer m) t, Recursively KFunctor t) =>
    Tree (Ann a) t -> m (Tree (ITerm a (UVarOf m)) t)
infer (Ann a x) =
    withDict (recursive :: RecursiveDict t (Infer m)) $
    withDict (recursive :: RecursiveDict t KFunctor) $
    (\s (InferRes xI t) -> ITerm a (IResult t s) xI)
    <$> getScope
    <*> inferBody
        (mapKWith (Proxy :: Proxy '[Recursively (Infer m), Recursively KFunctor])
            (\c -> infer c <&> (\i -> InferredChild i (i ^. iType)) & InferChild)
            x)
