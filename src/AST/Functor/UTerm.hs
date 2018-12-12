{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell #-}

module AST.Functor.UTerm
    ( UTerm(..), _UVar, _UTerm
    , UBody(..), uIndex, uBody
    ) where

import qualified Control.Lens as Lens

import           Prelude.Compat

-- Names modeled after unification-fd

data UBody a = UBody
    { _uIndex :: Int
    , _uBody :: a
    } deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makeLenses ''UBody

data UTerm f a
    = UVar (f a)
    | UTerm (UBody a)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makePrisms ''UTerm
