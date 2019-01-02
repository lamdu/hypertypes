{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, DataKinds, TemplateHaskell #-}

module AST.Class.Infer
    ( TypeAST, Infer(..)
    , TypeOf, inferNode
    , Inferred(..), iVal, iType, iAnn
    ) where

import AST.Class.Recursive
import AST.Knot (Knot, Tree, Tie, RunKnot)
import AST.Knot.Ann (Ann(..))
import AST.Unify (Unify(..), UVar)
import Control.Lens (makeLenses)
import Control.Lens.Operators

type family TypeAST (t :: Knot -> *) :: Knot -> *

data Inferred a v e = Inferred
    { _iVal  :: Tie e (Inferred a v)
    , _iType :: Tree v (TypeAST (RunKnot e))
    , _iAnn  :: a
    }
makeLenses ''Inferred

type TypeOf m t = Tree (UVar m) (TypeAST t)

class Recursive (Unify m) (TypeAST t) => Infer m t where
    infer :: Tree t (Ann a) -> m (TypeOf m t, Tree t (Inferred a (UVar m)))

inferNode :: Infer m t => Tree (Ann a) t -> m (Tree (Inferred a (UVar m)) t)
inferNode (Ann a x) = infer x <&> \(t, xI) -> Inferred xI t a
