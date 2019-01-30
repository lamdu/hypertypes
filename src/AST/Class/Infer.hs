{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts #-}

module AST.Class.Infer
    ( Infer(..), HasScope(..), LocalScopeType(..)
    ) where

import AST
import AST.Class.Unify (Unify(..), UVar)
import AST.Infer.Term

class HasScope m s where
    getScope :: m (Tree s (UVar m))

class LocalScopeType var scheme m where
    localScopeType :: var -> scheme -> m a -> m a

class
    (HasScope m (ScopeOf t), Recursive (Unify m) (TypeOf t)) =>
    Infer m t where

    infer :: Tree t (Ann a) -> m (Tree (UVar m) (TypeOf t), Tree t (ITerm a (UVar m)))
