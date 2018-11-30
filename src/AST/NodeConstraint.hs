{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses, FlexibleInstances, UndecidableInstances #-}

module AST.NodeConstraint
    ( NodeConstraint, IfChildNodes
    ) where

import AST

class constraint (Node f expr) => NodeConstraint constraint f expr
instance constraint (Node f expr) => NodeConstraint constraint f expr

-- | Used for standalone deriving clauses like
-- `deriving instance IfChildNodes Typ f Eq => Eq (Typ f)`
type IfChildNodes expr f constraint = ChildrenConstraint expr (NodeConstraint constraint f)
