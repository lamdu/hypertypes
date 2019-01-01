{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, TupleSections #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, RankNTypes #-}

module AST.Term.RowExtend
    ( RowExtend(..), rowKey, rowVal, rowRest
    , RowConstraints(..), RowKey
    , applyRowConstraints, rowStructureMismatch, inferRowExtend
    ) where

import AST.Class.Infer (Infer(..), TypeAST, TypeOf, inferNode, nodeType)
import AST.Class.Recursive (Recursive(..), RecursiveConstraint)
import AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import AST.Knot (Tree, Tie)
import AST.Knot.Ann (Ann)
import AST.Unify (Unify(..), UVar, newVar, unify, newTerm)
import AST.Unify.Constraints (HasTypeConstraints(..))
import AST.Unify.Term (UTerm(..))
import Algebra.Lattice (JoinSemiLattice(..))
import Control.DeepSeq (NFData)
import Control.Lens (Lens', makeLenses, contains)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Constraint (Constraint)
import Data.Proxy (Proxy(..))
import Data.Set (Set)
import GHC.Generics (Generic)
import Text.Show.Combinators ((@|), showCon)

import Prelude.Compat

-- | Row-extend primitive for use in both value-level and type-level
data RowExtend key val rest k = RowExtend
    { _rowKey :: key
    , _rowVal :: Tie k val
    , _rowRest :: Tie k rest
    } deriving Generic

makeLenses ''RowExtend
makeChildrenAndZipMatch [''RowExtend]

instance
    RecursiveConstraint (RowExtend key val rest) constraint =>
    Recursive constraint (RowExtend key val rest)

type Deps c key val rest k = ((c key, c (Tie k val), c (Tie k rest)) :: Constraint)
deriving instance Deps Eq   key val rest k => Eq   (RowExtend key val rest k)
deriving instance Deps Ord  key val rest k => Ord  (RowExtend key val rest k)
instance Deps Binary key val rest k => Binary (RowExtend key val rest k)
instance Deps NFData key val rest k => NFData (RowExtend key val rest k)

instance Deps Show key val rest k => Show (RowExtend key val rest k) where
    showsPrec p (RowExtend k v r) = (showCon "RowExtend" @| k @| v @| r) p

class Ord (RowConstraintsKey constraints) => RowConstraints constraints where
    type RowConstraintsKey constraints
    forbidden :: Lens' constraints (Set (RowConstraintsKey constraints))

type RowKey typ = RowConstraintsKey (TypeConstraintsOf typ)

applyRowConstraints ::
    ( Applicative m
    , constraint valTyp, constraint rowTyp
    , RowConstraints (TypeConstraintsOf rowTyp)
    ) =>
    Proxy constraint ->
    TypeConstraintsOf rowTyp ->
    (TypeConstraintsOf rowTyp -> TypeConstraintsOf valTyp) ->
    (RowKey rowTyp -> m r) ->
    (forall child. constraint child => TypeConstraintsOf child -> Tree p child -> m (Tree q child)) ->
    (Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) q -> r) ->
    Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) p ->
    m r
applyRowConstraints _ c toChildC err update cons (RowExtend k v rest)
    | c ^. forbidden . contains k = err k
    | otherwise =
        RowExtend k
        <$> update (c & forbidden .~ mempty & toChildC) v
        <*> update (c & forbidden . contains k .~ True) rest
        <&> cons

rowStructureMismatch ::
    Recursive (Unify m) rowTyp =>
    (Tree (RowExtend key valTyp rowTyp) (UVar m) -> m (Tree (UVar m) rowTyp)) ->
    (TypeConstraintsOf rowTyp, Tree (RowExtend key valTyp rowTyp) (UVar m)) ->
    (TypeConstraintsOf rowTyp, Tree (RowExtend key valTyp rowTyp) (UVar m)) ->
    m (Tree (RowExtend key valTyp rowTyp) (UVar m))
rowStructureMismatch mkExtend (c0, RowExtend k0 v0 r0) (c1, RowExtend k1 v1 r1) =
    do
        restVar <- c0 \/ c1 & UUnbound & newVar binding
        _ <- RowExtend k0 v0 restVar & mkExtend >>= unify r1
        RowExtend k1 v1 restVar & mkExtend
            >>= unify r0
            <&> RowExtend k0 v0

inferRowExtend ::
    forall m val rowTyp a.
    ( Infer m val
    , Unify m rowTyp
    , RowConstraints (TypeConstraintsOf rowTyp)
    ) =>
    (Tree (UVar m) rowTyp -> Tree (TypeAST val) (UVar m)) ->
    (Tree (RowExtend (RowKey rowTyp) (TypeAST val) rowTyp) (UVar m) -> Tree rowTyp (UVar m)) ->
    Tree (RowExtend (RowKey rowTyp) val val) (Ann a) ->
    m
    ( Tree (UVar m) rowTyp
    , Tree (RowExtend (RowKey rowTyp) val val) (Ann (TypeOf m val, a))
    )
inferRowExtend rowToTyp extendToRow (RowExtend k v r) =
    do
        vI <- inferNode v
        rI <- inferNode r
        restVar <-
            scopeConstraints (Proxy :: Proxy rowTyp)
            >>= newVar binding . UUnbound . (forbidden . contains k .~ True)
        _ <- rowToTyp restVar & newTerm >>= unify (rI ^. nodeType)
        RowExtend k (vI ^. nodeType) restVar & extendToRow & newTerm
            <&> (, RowExtend k vI rI)
