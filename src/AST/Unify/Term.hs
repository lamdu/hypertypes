{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}

module AST.Unify.Term
    ( TypeConstraints, TypeConstraintsAre
    , UTerm(..), _UVar, _UTerm, _UResolving
    , UTermBody(..), uBody, uConstraints
    ) where

import AST.Knot
import AST.Knot.Pure
import Control.Lens (makeLenses, makePrisms)

type family TypeConstraints (ast :: Knot -> *)

class TypeConstraints ast ~ constraints => TypeConstraintsAre constraints ast
instance TypeConstraints ast ~ constraints => TypeConstraintsAre constraints ast

data UTermBody v ast = UTermBody
    { _uConstraints :: TypeConstraints (RunKnot ast)
    , _uBody :: Tie ast v
    }
makeLenses ''UTermBody

data UTerm v ast
    = UUnbound (TypeConstraints (RunKnot ast))
    | USkolem (TypeConstraints (RunKnot ast))
    | UVar (v ast)
    | UTerm (UTermBody v ast)
    | UResolving (Tie ast v)
    | UResolved (Pure ast)
makePrisms ''UTerm
