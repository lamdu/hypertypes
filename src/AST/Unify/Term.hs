{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm, _UResolving
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
    | UResolving (UTermBody v ast)
    | UResolved (Pure ast)
    | -- Used in AST.Unify.STBinding.Save while converting to a pure binding.
      UConverted Int
makePrisms ''UTerm
