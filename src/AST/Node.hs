{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses, FlexibleInstances, UndecidableInstances #-}

module AST.Node
    ( Node, LeafNode
    , NodeConstraint
    ) where

import           Data.Functor.Const (Const)

-- | Each AST element is a `Node`
type Node f expr = f (expr f)

type LeafNode f expr = Node f (Const expr)

class constraint (Node f expr) => NodeConstraint constraint f expr
instance constraint (Node f expr) => NodeConstraint constraint f expr
