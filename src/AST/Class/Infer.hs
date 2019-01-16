{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, DataKinds, TemplateHaskell #-}

module AST.Class.Infer
    ( TypeOf, ScopeOf
    , ITerm(..), iVal, iType, iScope, iAnn
    , Infer(..), inferNode
    , HasScope(..), LocalScopeType(..)
    ) where

import AST.Class.Recursive
import AST.Class.Unify (Unify(..), UVar)
import AST.Knot (Knot, Tree, Tie, RunKnot)
import AST.Knot.Ann (Ann(..))
import Control.Lens (makeLenses)

import Prelude.Compat

type family TypeOf (t :: Knot -> *) :: Knot -> *
type family ScopeOf (t :: Knot -> *) :: Knot -> *

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
--
-- See also `AST.Class.Infer.Inferred.Inferred`, a newtype wrapper
-- knotted by `v` whose children are the types.
data ITerm a v e = ITerm
    { _iVal :: Tie e (ITerm a v)
    , _iType :: Tree v (TypeOf (RunKnot e))
    , _iScope :: Tree (ScopeOf (RunKnot e)) v
    , _iAnn :: a
    }
makeLenses ''ITerm

class HasScope m s where
    getScope :: m (Tree s (UVar m))

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
