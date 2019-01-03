{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, DataKinds, TemplateHaskell #-}

module AST.Class.Infer
    ( TypeOf, ScopeOf
    , ITerm(..), iVal, iType, iScope, iAnn
    , Infer(..), inferNode
    , HasScope(..), ScopeLookup(..), LocalScopeType(..)
    ) where

import AST.Class.Recursive
import AST.Knot (Knot, Tree, Tie, RunKnot)
import AST.Knot.Ann (Ann(..))
import AST.Unify (Unify(..), UVar)
import Control.Lens (makeLenses)
import Data.Proxy (Proxy)

import Prelude.Compat

type family TypeOf (t :: Knot -> *) :: Knot -> *
type family ScopeOf (t :: Knot -> *) :: Knot -> *

data ITerm a v e = ITerm
    { _iVal :: Tie e (ITerm a v)
    , _iType :: Tree v (TypeOf (RunKnot e))
    , _iScope :: Tree (ScopeOf (RunKnot e)) v
    , _iAnn :: a
    }
makeLenses ''ITerm

class HasScope m s where
    getScope :: m (Tree s (UVar m))

class ScopeLookup var expr where
    scopeType ::
        Recursive (Unify m) (TypeOf expr) =>
        Proxy expr -> var -> Tree (ScopeOf expr) (UVar m) -> m (Tree (UVar m) (TypeOf expr))

class LocalScopeType var scheme m where
    localScopeType :: var -> scheme -> m a -> m a

class
    (HasScope m (ScopeOf t), Recursive (Unify m) (TypeOf t)) =>
    Infer m t where

    infer :: Tree t (Ann a) -> m (Tree (UVar m) (TypeOf t), Tree t (ITerm a (UVar m)))

inferNode :: Infer m t => Tree (Ann a) t -> m (Tree (ITerm a (UVar m)) t)
inferNode (Ann a x) =
    (\s (t, xI) -> ITerm xI t s a)
    <$> getScope
    <*> infer x
