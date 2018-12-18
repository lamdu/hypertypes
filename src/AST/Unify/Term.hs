{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ConstraintKinds, UndecidableInstances #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm
    , UBody(..), uBody, uVisited
    , newUTerm
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.TH (makeChildren)
import           AST.Knot (Tie, Tree)
import qualified Control.Lens as Lens

import           Prelude.Compat

-- Names modeled after unification-fd

data UBody a = UBody
    { _uBody :: a
    , -- Used for occurs-check
      _uVisited :: Bool
    } deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makeLenses ''UBody

data UTerm f knot
    = UVar (f (UTerm f knot))
    | UTerm (UBody (Tie knot (UTerm f)))
Lens.makePrisms ''UTerm

makeChildren [''UTerm]

type UTermConstraints c f t = (c (f (UTerm f t)), SubTreeConstraint (UTerm f) t c)
deriving instance UTermConstraints Show f t => Show (UTerm f t)

newUTerm :: Tree t (UTerm v) -> Tree (UTerm v) t
newUTerm x =
    UTerm UBody
    { _uBody = x
    , _uVisited = False
    }
