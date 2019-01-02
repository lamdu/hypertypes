{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, DataKinds, TemplateHaskell #-}

module AST.Class.Infer
    ( TypeOf, Infer(..)
    , Inferred(..), iVal, iType, iAnn
    , inferNode
    ) where

import AST.Class.Recursive
import AST.Knot (Knot, Tree, Tie, RunKnot)
import AST.Knot.Ann (Ann(..))
import AST.Unify (Unify(..), UVar)
import Control.Lens (makeLenses)
import Control.Lens.Operators

type family TypeOf (t :: Knot -> *) :: Knot -> *

data Inferred a v e = Inferred
    { _iVal  :: Tie e (Inferred a v)
    , _iType :: Tree v (TypeOf (RunKnot e))
    , _iAnn  :: a
    }
makeLenses ''Inferred

class Recursive (Unify m) (TypeOf t) => Infer m t where
    infer :: Tree t (Ann a) -> m (Tree (UVar m) (TypeOf t), Tree t (Inferred a (UVar m)))

inferNode :: Infer m t => Tree (Ann a) t -> m (Tree (Inferred a (UVar m)) t)
inferNode (Ann a x) = infer x <&> \(t, xI) -> Inferred xI t a
