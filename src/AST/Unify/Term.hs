{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ConstraintKinds, UndecidableInstances, FlexibleContexts #-}

module AST.Unify.Term
    ( UTerm(..), _UVar, _UTerm, _UResolving
    , UTermBody(..), uBody, uLevel
    , InferLevel(..), _InferLevel
    ) where

import AST.Class.Children
import AST.Class.Recursive
import AST.Class.Recursive.TH (makeChildrenRecursive)
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

makeChildrenRecursive [''UTerm, ''UTermBody]

instance RecursiveConstraint (UTerm v) Children => Recursive Children (UTerm v)

deriving instance SubTreeConstraint (UTerm v) t Show => Show (UTerm v t)
deriving instance SubTreeConstraint (UTerm v) t Show => Show (UTermBody v t)
