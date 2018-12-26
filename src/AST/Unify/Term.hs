{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm, _UResolving
    , UTermBody(..), uBody, uConstraints
    , QuantificationScope(..), _QuantificationScope
    ) where

import AST.Knot
import AST.Knot.Pure
import Control.Lens (makeLenses, makePrisms)

import Prelude.Compat

newtype QuantificationScope = QuantificationScope Int
    deriving (Eq, Ord, Show)
makePrisms ''QuantificationScope

data UTermBody v ast = UTermBody
    { _uConstraints :: QuantificationScope
    , _uBody :: Tie ast v
    }
makeLenses ''UTermBody

data UTerm v ast
    = UUnbound QuantificationScope
    | USkolem QuantificationScope
    | UVar (v ast)
    | UTerm (UTermBody v ast)
    | UResolving (Tie ast v)
    | UResolved (Pure ast)
makePrisms ''UTerm
