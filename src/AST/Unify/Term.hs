{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ConstraintKinds, UndecidableInstances, FlexibleContexts #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm, _UResolving
    ) where

import           AST.Class.Children
import           AST.Class.Recursive
import           AST.Class.Recursive.TH (makeChildrenRecursive)
import           AST.Knot
import           AST.Knot.Pure
import qualified Control.Lens as Lens

import           Prelude.Compat

-- Names modeled after unification-fd

data UTerm v ast
    = UUnbound
    | UVar (v ast)
    | UTerm (Tie ast v)
    | UResolving (Tie ast v)
    | UResolved (Pure ast)

Lens.makePrisms ''UTerm

makeChildrenRecursive [''UTerm]

instance RecursiveConstraint (UTerm v) Children => Recursive Children (UTerm v)

deriving instance SubTreeConstraint (UTerm v) t Show => Show (UTerm v t)
