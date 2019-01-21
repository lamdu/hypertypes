{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances, ScopedTypeVariables, FlexibleInstances, RankNTypes #-}
{-# LANGUAGE ConstraintKinds, UndecidableSuperClasses, InstanceSigs, FlexibleContexts #-}

module AST.Class.Infer.Inferred
    ( Inferred(..), _Inferred
    , InferredChildConstraints
    ) where

import AST.Class.Children (Children(..), ChildrenWithConstraint)
import AST.Class.Infer (ITerm(..), TypeOf, ScopeOf)
import AST.Class.Recursive (Recursive(..))
import AST.Knot (Tree, RunKnot)
import Control.Lens (makePrisms)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

newtype Inferred ast a v = Inferred (Tree (ITerm a (RunKnot v)) ast)
makePrisms ''Inferred

class    (c (TypeOf ast), ChildrenWithConstraint (ScopeOf ast) c) => InferredChildConstraints c ast
instance (c (TypeOf ast), ChildrenWithConstraint (ScopeOf ast) c) => InferredChildConstraints c ast

instance Children (Inferred ast a) where
    type ChildrenConstraint (Inferred ast a) c = Recursive (InferredChildConstraints c) ast
    children ::
        forall f c n m.
        (Applicative f, Recursive (InferredChildConstraints c) ast) =>
        Proxy c ->
        (forall child. c child => Tree n child -> f (Tree m child)) ->
        Tree (Inferred ast a) n -> f (Tree (Inferred ast a) m)
    children p f (Inferred (ITerm b t s a)) =
        recursive (Proxy :: Proxy (InferredChildConstraints c ast)) $
        ITerm
        <$> children (Proxy :: Proxy (Recursive (InferredChildConstraints c)))
            (fmap (^. _Inferred) . children p f . Inferred)
            b
        <*> f t
        <*> children p f s
        <*> pure a
        <&> Inferred
