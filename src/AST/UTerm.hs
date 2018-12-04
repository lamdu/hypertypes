{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell #-}

module AST.UTerm
    ( UTerm(..), _UVar, _UTerm
    ) where

import qualified Control.Lens as Lens

import           Prelude.Compat

-- Names modeled after unification-fd

data UTerm f a
    = UVar (f a)
    | UTerm a
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makePrisms ''UTerm
