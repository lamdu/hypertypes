{-# LANGUAGE NoImplicitPrelude, ConstraintKinds, TypeFamilies #-}

module AST.Class.HasChildrenTypes
    ( HasChildrenTypes(..)
    ) where

import AST.Class.Applicative (KApplicative)
import AST.Knot (ChildrenTypesOf)
import Data.Constraint (Dict)
import Data.Proxy (Proxy)

type ChildrenTypesConstraints k =
    ( KApplicative k
    , ChildrenTypesOf k ~ k
    )

class HasChildrenTypes k where
    hasChildrenTypes ::
        Proxy k ->
        Dict (ChildrenTypesConstraints (ChildrenTypesOf k))
