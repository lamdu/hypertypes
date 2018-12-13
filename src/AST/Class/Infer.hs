{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, FlexibleContexts #-}

module AST.Class.Infer
    ( TypeAST, Infer(..)
    , INode, inferNode, nodeType
    , FuncType(..)
    ) where

import           AST.Class.Recursive (Recursive)
import           AST.Functor.Ann (Ann(..), ann)
import           AST.Functor.UTerm (UTerm)
import           AST.Node (Node)
import           AST.Unify (Unify(..), MonadUnify, Var)
import           Control.Lens (Lens', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators

import           Prelude.Compat

type family TypeAST (t :: (* -> *) -> *) :: (* -> *) -> *

type TypeOf m t = Node (UTerm (Var m)) (TypeAST t)
type INode v t a = Node (Ann (Node (UTerm v) (TypeAST t), a)) t

class (Recursive (Unify m) (TypeAST t), MonadUnify m) => Infer m t where
    infer :: t (Ann a) -> m (TypeOf m t, t (Ann (TypeOf m t, a)))

inferNode :: Infer m t => Node (Ann a) t -> m (INode (Var m) t a)
inferNode (Ann a x) =
    infer x <&> \(t, xI) -> Ann (t, a) xI

nodeType :: Lens' (INode v t a) (Node (UTerm v) (TypeAST t))
nodeType = ann . Lens._1

class FuncType t where
    funcType :: Prism' (t f) (Node f t, Node f t)
