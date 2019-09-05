module AST.Infer
    ( infer
    , module AST.Class.Infer
    , module AST.Class.Infer.Recursive
    , module AST.Infer.ScopeLevel
    , module AST.Infer.Term

    , -- | Exported only for SPECIALIZE pragmas
      inferH
    ) where

import AST
import AST.Class.Infer
import AST.Class.Infer.Recursive
import AST.Infer.ScopeLevel
import AST.Infer.Term
import AST.Unify (UVarOf)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | Perform Hindley-Milner type inference of a term
{-# INLINE infer #-}
infer ::
    forall m t a.
    Infer m t =>
    Tree (Ann a) t ->
    m (Tree (ITerm a (UVarOf m)) t)
infer (Ann a x) =
    withDict (inferContext (Proxy @m) (Proxy @t)) $
    inferBody (mapK (Proxy @(Infer m) #> inferH) x)
    <&> (\(xI, t) -> ITerm a t xI)

{-# INLINE inferH #-}
inferH ::
    Infer m t =>
    Tree (Ann a) t ->
    Tree (InferChild m (ITerm a (UVarOf m))) t
inferH c = infer c <&> (\i -> InferredChild i (i ^. iRes)) & InferChild
