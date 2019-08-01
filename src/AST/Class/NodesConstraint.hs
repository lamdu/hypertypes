{-# LANGUAGE NoImplicitPrelude, TypeOperators, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, FlexibleInstances #-}

module AST.Class.NodesConstraint
    ( NodesConstraint
    ) where

import AST

class    NodesConstraint k $ c => KNodesConstraint c k
instance NodesConstraint k $ c => KNodesConstraint c k
