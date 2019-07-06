{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts #-}

module AST.Class.Infer
    ( Infer(..), HasScope(..), LocalScopeType(..)
    , InferIn(..)
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf)
import AST.Infer.Term

newtype InferIn m k t =
    InferIn { runInferIn :: m (Tree (UVarOf m) (TypeOf (RunKnot t)), k t) }

class HasScope m s where
    getScope :: m (Tree s (UVarOf m))

class LocalScopeType var scheme m where
    localScopeType :: var -> scheme -> m a -> m a

class
    (HasScope m (ScopeOf t), Recursive (Unify m) (TypeOf t)) =>
    Infer m t where

    inferBody :: Tree t (InferIn m k) -> m (Tree (UVarOf m) (TypeOf t), Tree t k)
