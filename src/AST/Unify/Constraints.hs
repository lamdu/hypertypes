{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies, RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DefaultSignatures, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, TypeOperators, ScopedTypeVariables #-}

module AST.Unify.Constraints
    ( QuantificationScope(..), _QuantificationScope
    , TypeConstraints(..)
    , HasTypeConstraints(..)
    , TypeConstraintsAre
    ) where

import Algebra.Lattice (JoinSemiLattice(..))
import Algebra.PartialOrd (PartialOrd(..))
import AST.Class.Children (Children(..), ChildrenWithConstraint)
import AST.Class.Combinators (And)
import AST.Knot (Knot, Tree)
import Control.Lens (Lens', makePrisms)
import Data.Proxy (Proxy(..))

import Prelude.Compat

newtype QuantificationScope = QuantificationScope Int
    deriving (Eq, Show)
makePrisms ''QuantificationScope

instance PartialOrd QuantificationScope where
    QuantificationScope x `leq` QuantificationScope y = x >= y

instance JoinSemiLattice QuantificationScope where
    QuantificationScope x \/ QuantificationScope y = QuantificationScope (min x y)

class (PartialOrd c, JoinSemiLattice c) => TypeConstraints c where
    constraintsFromScope :: QuantificationScope -> c
    constraintsScope :: Lens' c QuantificationScope

instance TypeConstraints QuantificationScope where
    constraintsFromScope = id
    constraintsScope = id

class
    TypeConstraints (TypeConstraintsOf ast) =>
    HasTypeConstraints (ast :: Knot -> *) where

    type TypeConstraintsOf ast
    type TypeConstraintsOf ast = QuantificationScope
    propagateConstraints ::
        (Applicative m, ChildrenWithConstraint ast constraint) =>
        Proxy constraint ->
        TypeConstraintsOf ast ->
        (forall child. constraint child => TypeConstraintsOf child -> Tree p child -> m (Tree q child)) ->
        Tree ast p -> m (Tree ast q)
    default propagateConstraints ::
        forall m constraint p q.
        ( TypeConstraintsOf ast ~ QuantificationScope
        , ChildrenWithConstraint ast (constraint `And` HasTypeConstraints)
        , Applicative m
        ) =>
        Proxy constraint ->
        TypeConstraintsOf ast ->
        (forall child. constraint child => TypeConstraintsOf child -> Tree p child -> m (Tree q child)) ->
        Tree ast p -> m (Tree ast q)
    propagateConstraints _ constraints update =
        children (Proxy :: Proxy (constraint `And` HasTypeConstraints))
        (update (constraintsFromScope constraints))

class TypeConstraintsOf ast ~ constraints => TypeConstraintsAre constraints ast
instance TypeConstraintsOf ast ~ constraints => TypeConstraintsAre constraints ast
