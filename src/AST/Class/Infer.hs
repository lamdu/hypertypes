{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, TypeOperators #-}

module AST.Class.Infer
    ( TypeAST, Infer(..)
    , INode, inferNode, nodeType
    , HasTypeAST1(..), Infer1(..)
    , FuncType(..)
    ) where

import           AST.Functor.Ann (Ann(..), ann)
import           AST.Functor.UTerm (UTerm)
import           AST.Node (Node)
import           AST.Unify (Unify(..), Var)
import           Control.Lens (Lens', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

type family TypeAST (t :: (* -> *) -> *) :: (* -> *) -> *

type TypeOf m t = Node (UTerm (Var m)) (TypeAST t)
type INode v t a = Node (Ann (Node (UTerm v) (TypeAST t), a)) t

class Unify m (TypeAST t) => Infer m t where
    infer :: t (Ann a) -> m (TypeOf m t, t (Ann (TypeOf m t, a)))

inferNode :: Infer m t => Node (Ann a) t -> m (INode (Var m) t a)
inferNode (Ann a x) =
    infer x <&> \(t, xI) -> Ann (t, a) xI

nodeType :: Lens' (INode v t a) (Node (UTerm v) (TypeAST t))
nodeType = ann . Lens._1

class HasTypeAST1 t where
    type family TypeAST1 t :: (* -> *) -> *
    type family TypeASTIndexConstraint t :: * -> Constraint
    typeAst :: Proxy (t k) -> Dict (TypeAST (t k) ~ TypeAST1 t)

class HasTypeAST1 t => Infer1 m t where
    inferMonad :: TypeASTIndexConstraint t i :- Infer m (t i)

class FuncType t where
    funcType :: Prism' (t f) (Node f t, Node f t)
