{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, TupleSections #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, RankNTypes #-}

module AST.Term.Row
    ( RowConstraints(..), RowKey
    , RowExtend(..), eKey, eVal, eRest
    , applyRowExtendConstraints, rowExtendStructureMismatch
    , inferRowExtend
    , rowElementInfer
    ) where

import AST.Class.Infer (Infer(..), ITerm, TypeOf, inferNode, iType)
import AST.Class.Recursive (Recursive(..), RecursiveConstraint)
import AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import AST.Knot (Tree, Tie)
import AST.Knot.Ann (Ann)
import AST.Unify (Unify(..), UVar, unify, newTerm, newUnbound)
import AST.Unify.Binding (Binding(..))
import AST.Unify.Constraints (TypeConstraints(..), HasTypeConstraints(..), ScopeConstraintsMonad(..))
import AST.Unify.Term (UTerm(..))
import Algebra.Lattice (JoinSemiLattice(..))
import Control.DeepSeq (NFData)
import Control.Lens (Lens', makeLenses, contains)
import Control.Lens.Operators
import Control.Monad (when)
import Data.Binary (Binary)
import Data.Constraint (Constraint)
import Data.Proxy (Proxy(..))
import Data.Set (Set)
import GHC.Generics (Generic)
import Text.Show.Combinators ((@|), showCon)

import Prelude.Compat

class
    (Ord (RowConstraintsKey constraints), TypeConstraints constraints) =>
    RowConstraints constraints where

    type RowConstraintsKey constraints
    forbidden :: Lens' constraints (Set (RowConstraintsKey constraints))

type RowKey typ = RowConstraintsKey (TypeConstraintsOf typ)

-- | Row-extend primitive for use in both value-level and type-level
data RowExtend key val rest k = RowExtend
    { _eKey :: key
    , _eVal :: Tie k val
    , _eRest :: Tie k rest
    } deriving Generic

makeLenses ''RowExtend
makeChildrenAndZipMatch ''RowExtend

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

-- Helpers for Unify instances of type-level RowExtends:

applyRowExtendConstraints ::
    ( Applicative m
    , constraint valTyp, constraint rowTyp
    , RowConstraints (TypeConstraintsOf rowTyp)
    ) =>
    Proxy constraint ->
    TypeConstraintsOf rowTyp ->
    (TypeConstraintsOf rowTyp -> TypeConstraintsOf valTyp) ->
    (RowKey rowTyp -> m ()) ->
    (forall child. constraint child => TypeConstraintsOf child -> Tree p child -> m (Tree q child)) ->
    Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) p ->
    m (Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) q)
applyRowExtendConstraints _ c toChildC err update (RowExtend k v rest) =
    when (c ^. forbidden . contains k) (err k)
    *>
    (RowExtend k
        <$> update (c & forbidden .~ mempty & toChildC) v
        <*> update (c & forbidden . contains k .~ True) rest
    )

rowExtendStructureMismatch ::
    Recursive (Unify m) rowTyp =>
    (Tree (RowExtend key valTyp rowTyp) (UVar m) -> m (Tree (UVar m) rowTyp)) ->
    (TypeConstraintsOf rowTyp, Tree (RowExtend key valTyp rowTyp) (UVar m)) ->
    (TypeConstraintsOf rowTyp, Tree (RowExtend key valTyp rowTyp) (UVar m)) ->
    m ()
rowExtendStructureMismatch mkExtend (c0, RowExtend k0 v0 r0) (c1, RowExtend k1 v1 r1) =
    do
        restVar <- c0 \/ c1 & UUnbound & newVar binding
        _ <- RowExtend k0 v0 restVar & mkExtend >>= unify r1
        _ <- RowExtend k1 v1 restVar & mkExtend >>= unify r0
        pure ()

-- Helper for Infer instances of value-level RowExtends.
-- An Infer instance for RowExtend isn't suitable because the term language
-- may have separate row-extends (for example one for records and one for pattern matches)
inferRowExtend ::
    forall m val rowTyp a.
    ( Infer m val
    , Unify m rowTyp
    , RowConstraints (TypeConstraintsOf rowTyp)
    ) =>
    (Tree (UVar m) rowTyp -> Tree (TypeOf val) (UVar m)) ->
    (Tree (RowExtend (RowKey rowTyp) (TypeOf val) rowTyp) (UVar m) -> Tree rowTyp (UVar m)) ->
    Tree (RowExtend (RowKey rowTyp) val val) (Ann a) ->
    m
    ( Tree (UVar m) rowTyp
    , Tree (RowExtend (RowKey rowTyp) val val) (ITerm a (UVar m))
    )
inferRowExtend rowToTyp extendToRow (RowExtend k v r) =
    do
        vI <- inferNode v
        rI <- inferNode r
        restVar <-
            scopeConstraints
            >>= newVar binding . UUnbound . (forbidden . contains k .~ True)
        _ <- rowToTyp restVar & newTerm >>= unify (rI ^. iType)
        RowExtend k (vI ^. iType) restVar & extendToRow & newTerm
            <&> (, RowExtend k vI rI)

-- Helper for infering row usages of a row element,
-- such as getting a field from a record or injecting into a sum type.
-- Returns a unification variable for the element and for the whole row.
rowElementInfer ::
    forall m valTyp rowTyp.
    ( Unify m valTyp
    , Unify m rowTyp
    , RowConstraints (TypeConstraintsOf rowTyp)
    ) =>
    (Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) (UVar m) -> Tree rowTyp (UVar m)) ->
    RowKey rowTyp ->
    m (Tree (UVar m) valTyp, Tree (UVar m) rowTyp)
rowElementInfer extendToRow k =
    do
        restVar <-
            scopeConstraints
            >>= newVar binding . UUnbound . (forbidden . contains k .~ True)
        part <- newUnbound
        whole <- RowExtend k part restVar & extendToRow & newTerm
        pure (part, whole)
