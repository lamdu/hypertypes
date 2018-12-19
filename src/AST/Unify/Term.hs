{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ConstraintKinds, UndecidableInstances, FlexibleContexts #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm
    , VTerm(..), _VVar, _VTerm, _VResolving
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Recursive
import           AST.Class.Recursive.TH (makeChildrenRecursive)
import           AST.Knot (Tie)
import           AST.Knot.Pure
import qualified Control.Lens as Lens

import           Prelude.Compat

-- Names modeled after unification-fd

data UTerm f ast
    = UVar (f (VTerm f ast))
    | UTerm (Tie ast (UTerm f))

data VTerm f ast
    = VVar (f (VTerm f ast))
    | VTerm (Tie ast (UTerm f))
    | VResolving (Tie ast (UTerm f))
    | VResolved (Pure ast)

Lens.makePrisms ''UTerm
Lens.makePrisms ''VTerm

makeChildrenRecursive [''UTerm, ''VTerm]

instance Traversable f => Recursive Children (UTerm f)
instance Traversable f => Recursive Children (VTerm f)

type Deps t f = (Show (Tie t (UTerm f)), Show (f (VTerm f t)), Show (Tie t Pure))

deriving instance Deps t f => Show (UTerm f t)
deriving instance Deps t f => Show (VTerm f t)
