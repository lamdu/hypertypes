{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Unify.Term
    ( UTerm(..)
        , _UUnbound, _USkolem, _UVar, _UTerm, _UInstantiated
        , _UResolving, _UResolved, _UConverted
    , UTermBody(..), uBody, uConstraints
    ) where

import AST
import AST.Unify.Constraints (TypeConstraintsOf)
import Control.Lens (makeLenses, makePrisms)

import Prelude.Compat

data UTermBody v ast = UTermBody
    { _uConstraints :: TypeConstraintsOf (RunKnot ast)
    , _uBody :: Tie ast v
    }
makeLenses ''UTermBody

data UTerm v ast
    = UUnbound (TypeConstraintsOf (RunKnot ast))
    | USkolem (TypeConstraintsOf (RunKnot ast))
    | UVar (v ast)
    | UTerm (UTermBody v ast)
    | UInstantiated (v ast)
      -- ^ Temporary state during instantiation indicating which fresh
      -- unification variable a skolem is mapped to
    | UResolving (UTermBody v ast)
    | UResolved (Pure ast)
    | -- Used in AST.Unify.STBinding.Save while converting to a pure binding.
      UConverted Int
makePrisms ''UTerm
