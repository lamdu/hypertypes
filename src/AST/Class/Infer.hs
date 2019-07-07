{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies #-}

module AST.Class.Infer
    ( Infer(..), HasScope(..), LocalScopeType(..)
    , InferredChild(..), inType, inRep
    , InferChild(..), _InferChild
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf)
import AST.Infer.Term
import Control.Lens (Lens, makeLenses, makePrisms)
import Control.Lens.Operators

data InferredChild v k t = InferredChild
    { _inType :: !(Tree v (TypeOf (RunKnot t)))
    , -- Representing the inferred child in the resulting node
      __inRep :: !(k t)
    }
makeLenses ''InferredChild

inRep ::
    TypeOf (RunKnot t0) ~ TypeOf (RunKnot t1) =>
    Lens (InferredChild v k0 t0) (InferredChild v k1 t1) (k0 t0) (k1 t1)
inRep f (InferredChild t r) =
    f r <&> InferredChild t

newtype InferChild m k t =
    InferChild { inferChild :: m (InferredChild (UVarOf m) k t) }
makePrisms ''InferChild

class HasScope m s where
    getScope :: m (Tree s (UVarOf m))

class LocalScopeType var scheme m where
    localScopeType :: var -> scheme -> m a -> m a

class
    (HasScope m (ScopeOf t), Recursive (Unify m) (TypeOf t)) =>
    Infer m t where

    inferBody ::
        Tree t (InferChild m k) ->
        m (Tree (UVarOf m) (TypeOf t), Tree t k)
