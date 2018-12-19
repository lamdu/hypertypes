{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ConstraintKinds, UndecidableInstances, FlexibleContexts #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm
    , VTerm(..), _VVar, _VTerm, _VResolving
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
    = UVar (v ast)
    | UTerm (Tie ast (UTerm v))

data VTerm v ast
    = VVar (v ast)
    | VTerm (Tie ast (UTerm v))
    | VResolving (Tie ast (UTerm v))
    | VResolved (Pure ast)

Lens.makePrisms ''UTerm
Lens.makePrisms ''VTerm

makeChildrenRecursive [''UTerm, ''VTerm]

instance ChildrenWithConstraint v (Recursive Children) => Recursive Children (UTerm v)
instance ChildrenWithConstraint v (Recursive Children) => Recursive Children (VTerm v)

type Deps t v = (Show (Tie t (UTerm v)), Show (v t), Show (Tie t Pure))

deriving instance Deps t f => Show (UTerm f t)
deriving instance Deps t f => Show (VTerm f t)
