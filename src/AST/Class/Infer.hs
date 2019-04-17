{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts #-}

module AST.Class.Infer
    ( Infer(..), HasScope(..), LocalScopeType(..)
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf)
import AST.Infer.Term

class HasScope m s where
    getScope :: m (Tree s (UVarOf m))

class LocalScopeType var scheme m where
    localScopeType :: var -> scheme -> m a -> m a

class
    (HasScope m (ScopeOf t), Recursive (Unify m) (TypeOf t)) =>
    Infer m t where

    inferBody :: Tree t (Ann a) -> m (Tree (UVarOf m) (TypeOf t), Tree t (ITerm a (UVarOf m)))
