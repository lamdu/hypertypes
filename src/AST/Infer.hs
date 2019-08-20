{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

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
import AST.Unify (UVarOf)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

import Prelude.Compat

{-# INLINE infer #-}
infer ::
    forall m t a.
    Infer m t =>
    Tree (Ann a) t ->
    m (Tree (ITerm a (UVarOf m)) t)
infer (Ann a x) =
    withDict (inferRecursive (Proxy @m) (Proxy @t)) $
    inferBody
        (mapKWith (Proxy @(Infer m))
            (\c -> infer c <&> (\i -> InferredChild i (i ^. iRes)) & InferChild)
            x)
    <&> (\(InferRes xI t) -> ITerm a t xI)
