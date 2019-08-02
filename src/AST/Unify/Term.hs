{-# LANGUAGE TemplateHaskell, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}

module AST.Unify.Term
    ( UTerm(..)
        , _UUnbound, _USkolem, _UToVar, _UTerm, _UInstantiated
        , _UResolving, _UResolved, _UConverted
    , UTermDeps
    , UTermBody(..), uBody, uConstraints
    ) where

import AST
import AST.Unify.Constraints (TypeConstraintsOf)
import Control.Lens (makeLenses, makePrisms)
import Data.Constraint (Constraint)

import Prelude.Compat

data UTermBody v ast = UTermBody
    { _uConstraints :: TypeConstraintsOf (RunKnot ast)
    , _uBody :: Node ast v
    }
makeLenses ''UTermBody

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
makePrisms ''UTerm

type UTermDeps c v ast =
    (( BodyDeps c v ast
     , c (v ast)
     , c (Node ast Pure)
     ) :: Constraint)

deriving instance UTermDeps Eq v ast => Eq (UTerm v ast)
deriving instance UTermDeps Ord v ast => Ord (UTerm v ast)
deriving instance UTermDeps Show v ast => Show (UTerm v ast)

type BodyDeps c v ast =
    ( ( c (TypeConstraintsOf (RunKnot ast))
      , c (Node ast v)
      ) :: Constraint
    )
deriving instance BodyDeps Eq v ast => Eq (UTermBody v ast)
deriving instance BodyDeps Ord v ast => Ord (UTermBody v ast)
deriving instance BodyDeps Show v ast => Show (UTermBody v ast)
