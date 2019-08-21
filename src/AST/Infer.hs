module AST.Infer
    ( module AST.Class.Infer
    , module AST.Infer.ScopeLevel
    , module AST.Infer.Term
    , infer

    , -- Exported for SPECIALIZE pragmas
      inferH
    ) where

import AST
import AST.Class.Infer
import AST.Infer.ScopeLevel
import AST.Infer.Term
import AST.Unify (UVarOf)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

{-# INLINE infer #-}
infer ::
    forall m t a.
    Infer m t =>
    Tree (Ann a) t ->
    m (Tree (ITerm a (UVarOf m)) t)
infer (Ann a x) =
    inferRecursive (Proxy @m) (Proxy @t) $
    inferBody (mapKWith (Proxy @(Infer m)) inferH x)
    <&> (\(InferRes xI t) -> ITerm a t xI)

{-# INLINE inferH #-}
inferH ::
    Infer m t =>
    Tree (Ann a) t ->
    Tree (InferChild m (ITerm a (UVarOf m))) t
inferH c = infer c <&> (\i -> InferredChild i (i ^. iRes)) & InferChild
