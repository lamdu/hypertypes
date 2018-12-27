{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module AST.Unify.Term
    ( TypeConstraintsOf, TypeConstraintsAre
    , UTerm(..), _UVar, _UTerm, _UResolving
    , UTermBody(..), uBody, uConstraints
    ) where

import AST.Knot
import AST.Knot.Pure
import Control.Lens (makeLenses, makePrisms)

type family TypeConstraintsOf (ast :: Knot -> *)

class TypeConstraintsOf ast ~ constraints => TypeConstraintsAre constraints ast
instance TypeConstraintsOf ast ~ constraints => TypeConstraintsAre constraints ast

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
    | UResolving (Tie ast v)
    | UResolved (Pure ast)
makePrisms ''UTerm
