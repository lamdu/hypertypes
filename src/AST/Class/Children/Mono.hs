{-# LANGUAGE NoImplicitPrelude, TypeFamilies, ScopedTypeVariables #-}

module AST.Class.Children.Mono
    ( ChildOf, monoChildren
    ) where

import           AST.Class.Children (Children(..), ChildrenWithConstraint)
import           AST.Node (Node)
import           Control.Lens (Traversal)
import           Data.Proxy (Proxy(..))

type family ChildOf (expr :: (* -> *) -> *) :: (* -> *) -> *

monoChildren ::
    forall expr n m.
    (ChildrenWithConstraint expr ((~) (ChildOf expr))) =>
    Traversal (expr n) (expr m) (Node n (ChildOf expr)) (Node m (ChildOf expr))
monoChildren = children (Proxy :: Proxy ((~) (ChildOf expr)))
