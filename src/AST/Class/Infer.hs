{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts, TemplateHaskell #-}

module AST.Class.Infer
    ( Infer(..), HasScope(..), LocalScopeType(..)
    , InferredChild(..), inType, inRep
    , InferChild(..), _InferChild
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf)
import AST.Infer.Term
import Control.Lens (makeLenses, makePrisms)

data InferredChild v k t = InferredChild
    { _inType :: !(Tree v (TypeOf (RunKnot t)))
    , -- Representing the inferred child in the resulting node
      _inRep :: !(k t)
    }
makeLenses ''InferredChild

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
