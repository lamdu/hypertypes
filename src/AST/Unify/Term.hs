{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm, _UResolving
    , UTermBody(..), uBody, uLevel
    , InferLevel(..), _InferLevel
    ) where

import AST.Knot
import AST.Knot.Pure
import Control.Lens (makeLenses, makePrisms)

import Prelude.Compat

newtype InferLevel = InferLevel Int
    deriving (Eq, Ord, Show)
makePrisms ''InferLevel

data UTermBody v ast = UTermBody
    { _uLevel :: InferLevel
    , _uBody :: Tie ast v
    }
makeLenses ''UTermBody

data UTerm v ast
    = UUnbound InferLevel
    | USkolem InferLevel
    | UVar (v ast)
    | UTerm (UTermBody v ast)
    | UResolving (Tie ast v)
    | UResolved (Pure ast)
makePrisms ''UTerm
