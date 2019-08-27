{-# LANGUAGE TemplateHaskell, FlexibleContexts, UndecidableInstances #-}

module AST.Unify.Term
    ( UTerm(..)
        , _UUnbound, _USkolem, _UToVar, _UTerm, _UInstantiated
        , _UResolving, _UResolved, _UConverted
    , UTermBody(..), uBody, uConstraints
    ) where

import AST
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.Unify.Constraints (TypeConstraintsOf)
import Control.Lens (makeLenses, makePrisms)
import GHC.Generics (Generic)

import Prelude.Compat

data UTermBody v ast = UTermBody
    { _uConstraints :: TypeConstraintsOf (RunKnot ast)
    , _uBody :: Node ast v
    } deriving Generic

makeLenses ''UTermBody
makeCommonInstances ''UTermBody

-- | A unification term pointed by a unification variable
data UTerm v ast
    = UUnbound (TypeConstraintsOf (RunKnot ast))
      -- ^ Unbound variable with at least the given constraints
    | USkolem (TypeConstraintsOf (RunKnot ast))
      -- ^ A variable bound by a rigid quantified variable with
      -- *exactly* the given constraints
    | UToVar (v ast)
      -- ^ Unified with another variable (union-find)
    | UTerm (UTermBody v ast)
      -- ^ Known type term with unification variables as children
    | UInstantiated (v ast)
      -- ^ Temporary state during instantiation indicating which fresh
      -- unification variable a skolem is mapped to
    | UResolving (UTermBody v ast)
      -- ^ Temporary state while unification term is being traversed,
      -- if it occurs inside itself (detected via state still being
      -- UResolving), then the type is an infinite type
    | UResolved (Pure ast)
      -- ^ Final resolved state. `AST.Unify.applyBindings` resolved to
      -- this expression (allowing caching/sharing)
    | UConverted Int
      -- ^ Temporary state used in "AST.Unify.Binding.ST.Save" while
      -- converting to a pure binding
    deriving Generic

makePrisms ''UTerm
makeCommonInstances ''UTerm
