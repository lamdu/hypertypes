{-# LANGUAGE NoImplicitPrelude, TypeFamilies, ScopedTypeVariables, DataKinds #-}

module AST.Class.Children.Mono
    ( ChildOf, monoChildren
    ) where

import AST.Class.Children (Children(..), ChildrenWithConstraint)
import AST.Knot (Knot, Tree)
import Control.Lens (Traversal)
import Data.Proxy (Proxy(..))

type family ChildOf (expr :: Knot -> *) :: Knot -> *

monoChildren ::
    forall expr n m.
    (ChildrenWithConstraint expr ((~) (ChildOf expr))) =>
    Traversal (Tree expr n) (Tree expr m) (Tree n (ChildOf expr)) (Tree m (ChildOf expr))
monoChildren = children (Proxy :: Proxy ((~) (ChildOf expr)))
