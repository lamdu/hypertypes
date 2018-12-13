{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell #-}

module AST.Knot.UTerm
    ( UTerm(..), _UVar, _UTerm
    , UBody(..), uBody, uVisited
    , newUTerm
    ) where

import           AST.Node (Node)
import qualified Control.Lens as Lens

import           Prelude.Compat

-- Names modeled after unification-fd

data UBody a = UBody
    { _uBody :: a
    , -- Used for occurs-check
      _uVisited :: Bool
    } deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makeLenses ''UBody

data UTerm f a
    = UVar (f a)
    | UTerm (UBody a)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makePrisms ''UTerm

newUTerm :: t (UTerm v) -> Node (UTerm v) t
newUTerm x =
    UTerm UBody
    { _uBody = x
    , _uVisited = False
    }
