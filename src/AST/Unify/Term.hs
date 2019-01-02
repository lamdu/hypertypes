{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm, _UResolving
    , UTermBody(..), uBody, uConstraints
    ) where

import AST.Knot (Tie, RunKnot)
import AST.Knot.Pure (Pure)
import AST.Unify.Constraints (TypeConstraintsOf)
import Control.Lens (makeLenses, makePrisms)

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
makePrisms ''UTerm
