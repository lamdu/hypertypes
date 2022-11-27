{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Unification terms.
--
-- These represent the known state of a unification variable.
module Hyper.Unify.Term
    ( UTerm (..)
    , _UUnbound
    , _USkolem
    , _UToVar
    , _UTerm
    , _UInstantiated
    , _UResolving
    , _UResolved
    , _UConverted
    , UTermBody (..)
    , uBody
    , uConstraints
    ) where

import Hyper
import Hyper.Unify.Constraints (TypeConstraintsOf)

import Hyper.Internal.Prelude

-- | A unification term with a known body
data UTermBody v ast = UTermBody
    { _uConstraints :: TypeConstraintsOf (GetHyperType ast)
    , _uBody :: ast :# v
    }
    deriving (Generic)

-- | A unification term pointed by a unification variable
data UTerm v ast
    = -- | Unbound variable with at least the given constraints
      UUnbound (TypeConstraintsOf (GetHyperType ast))
    | -- | A variable bound by a rigid quantified variable with
      -- *exactly* the given constraints
      USkolem (TypeConstraintsOf (GetHyperType ast))
    | -- | Unified with another variable (union-find)
      UToVar (v ast)
    | -- | Known type term with unification variables as children
      UTerm (UTermBody v ast)
    | -- | Temporary state during instantiation indicating which fresh
      -- unification variable a skolem is mapped to
      UInstantiated (v ast)
    | -- | Temporary state while unification term is being traversed,
      -- if it occurs inside itself (detected via state still being
      -- UResolving), then the type is an infinite type
      UResolving (UTermBody v ast)
    | -- | Final resolved state. `Hyper.Unify.applyBindings` resolved to
      -- this expression (allowing caching/sharing)
      UResolved (Pure ast)
    | -- | Temporary state used in "Hyper.Unify.Binding.ST.Save" while
      -- converting to a pure binding
      UConverted Int
    deriving (Generic)

makePrisms ''UTerm
makeLenses ''UTermBody
makeCommonInstances [''UTerm, ''UTermBody]
