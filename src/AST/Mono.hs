{-# LANGUAGE NoImplicitPrelude, TypeFamilies, ScopedTypeVariables #-}

module AST.Mono
    ( ChildOf, monoChildren
    ) where

import           AST (Node, Children(..), ChildrenWithConstraint)
import           Control.Lens (Traversal)
import           Data.Proxy (Proxy(..))

type family ChildOf (expr :: (* -> *) -> *) :: (* -> *) -> *

monoChildren ::
    forall expr n m.
    (ChildrenWithConstraint expr ((~) (ChildOf expr))) =>
    Traversal (expr n) (expr m) (Node n (ChildOf expr)) (Node m (ChildOf expr))
monoChildren = children (Proxy :: Proxy ((~) (ChildOf expr)))
