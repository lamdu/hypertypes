{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, FlexibleContexts, DataKinds #-}

module AST.Class.Infer
    ( TypeAST, Infer(..)
    , INode, inferNode, nodeType
    , FuncType(..)
    ) where

import           AST.Class.Recursive (Recursive)
import           AST.Knot (Knot, Tree)
import           AST.Knot.Ann (Ann(..), ann)
import           AST.Knot.UTerm (UTerm)
import           AST.Unify (Unify(..), UniVar)
import           Control.Lens (Lens', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators

import           Prelude.Compat

type family TypeAST (t :: Knot -> *) :: Knot -> *

type TypeOf m t = Tree (UTerm (UniVar m)) (TypeAST t)
type INode v t a = Tree (Ann (Tree (UTerm v) (TypeAST t), a)) t

class (Recursive (Unify m) (TypeAST t), Functor m) => Infer m t where
    infer :: Tree t (Ann a) -> m (TypeOf m t, Tree t (Ann (TypeOf m t, a)))

inferNode :: Infer m t => Tree (Ann a) t -> m (INode (UniVar m) t a)
inferNode (Ann a x) =
    infer x <&> \(t, xI) -> Ann (t, a) xI

nodeType :: Lens' (INode v t a) (Tree (UTerm v) (TypeAST t))
nodeType = ann . Lens._1

class FuncType t where
    funcType :: Prism' (Tree t f) (Tree f t, Tree f t)
