{-# LANGUAGE NoImplicitPrelude, ConstraintKinds, TypeFamilies #-}

module AST.Class.HasChildrenTypes
    ( HasChildrenTypes(..)
    ) where

import AST.Class.Applicative (KApplicative)
import AST.Class.Traversable (KTraversable)
import AST.Knot (ChildrenTypesOf)
import Data.Constraint (Dict)
import Data.Proxy (Proxy)

type ChildrenTypesConstraints k =
    ( ChildrenTypesOf k ~ k
    , KApplicative k
    , KTraversable k
    )

class HasChildrenTypes k where
    hasChildrenTypes ::
        Proxy k ->
        Dict (ChildrenTypesConstraints (ChildrenTypesOf k))
