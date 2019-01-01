{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, DataKinds #-}

module AST.Class.Infer
    ( TypeAST, Infer(..), MonadLevel(..)
    , TypeOf, INode, inferNode, nodeType
    ) where

import           AST.Class.Recursive
import           AST.Knot (Knot, Tree)
import           AST.Knot.Ann (Ann(..), ann)
import           AST.Unify (MonadUnify, Unify(..), UVar)
import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators

import           Prelude.Compat

type family TypeAST (t :: Knot -> *) :: Knot -> *

type TypeOf m t = Tree (UVar m) (TypeAST t)
type INode v t a = Tree (Ann (Tree v (TypeAST t), a)) t

class MonadUnify m => MonadLevel m where
    localLevel :: m a -> m a

class (Recursive (Unify m) (TypeAST t), MonadUnify m) => Infer m t where
    infer :: Tree t (Ann a) -> m (TypeOf m t, Tree t (Ann (TypeOf m t, a)))

inferNode :: Infer m t => Tree (Ann a) t -> m (INode (UVar m) t a)
inferNode (Ann a x) =
    infer x <&> \(t, xI) -> Ann (t, a) xI

nodeType :: Lens' (INode v t a) (Tree v (TypeAST t))
nodeType = ann . Lens._1
