{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ConstraintKinds, UndecidableInstances #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm
    , VTerm(..), _VVar, _VTerm, _VResolving
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Recursive
import           AST.Class.TH (makeChildren)
import           AST.Knot (Tie)
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

Lens.makePrisms ''UTerm
Lens.makePrisms ''VTerm

makeChildren [''UTerm, ''VTerm]

instance Traversable f => Recursive Children (UTerm f)
instance Traversable f => Recursive Children (VTerm f)

deriving instance (Show (Tie t (UTerm f)), Show (f (VTerm f t))) => Show (UTerm f t)
deriving instance (Show (Tie t (UTerm f)), Show (f (VTerm f t))) => Show (VTerm f t)
