{-# LANGUAGE NoImplicitPrelude #-}

module AST.Node
    ( Node, LeafNode
    ) where

import           Data.Functor.Const (Const)

-- | Each AST element is a `Node`
type Node f expr = f (expr f)

type LeafNode f leaf = Node f (Const leaf)
