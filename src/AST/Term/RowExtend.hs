{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, DataKinds, TupleSections #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module AST.Term.RowExtend
    ( RowExtend(..), rowKey, rowVal, rowRest
    , updateRowChildConstraints, rowStructureMismatch, inferRowExtend
    ) where

import Algebra.Lattice (JoinSemiLattice(..))
import AST.Class.Infer (Infer(..), TypeAST, TypeOf, inferNode, nodeType)
import AST.Class.Recursive (Recursive(..), RecursiveConstraint, RecursiveDict)
import AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import AST.Knot (Tree, Tie)
import AST.Knot.Ann (Ann)
import AST.Unify (Unify(..), UVar, updateConstraints, newVar, unify, scopeConstraintsForType, newTerm)
import AST.Unify.Term (TypeConstraints, UTermBody(..), UTerm(..))
import Control.DeepSeq (NFData)
import Control.Lens (cloneLens, makeLenses)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Constraint (Constraint, withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

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
deriving instance Deps Show key val rest k => Show (RowExtend key val rest k)
instance Deps Binary key val rest k => Binary (RowExtend key val rest k)
instance Deps NFData key val rest k => NFData (RowExtend key val rest k)

type instance TypeConstraints (RowExtend key valTyp rowTyp) = TypeConstraints rowTyp

updateRowChildConstraints ::
    forall m key valTyp rowTyp.
    (Unify m valTyp, Unify m rowTyp) =>
    (key -> TypeConstraints rowTyp -> TypeConstraints rowTyp) ->
    TypeConstraints rowTyp ->
    Tree (RowExtend key valTyp rowTyp) (UVar m) ->
    m (Tree (RowExtend key valTyp rowTyp) (UVar m))
updateRowChildConstraints forbid c (RowExtend k v r) =
    RowExtend k
    <$> updateConstraints valConstraints v
    <*> updateConstraints (forbid k c) r
    where
        pm = Proxy :: Proxy m
        valConstraints =
            c ^. cloneLens (typeScopeConstraints pm (Proxy :: Proxy rowTyp))
            & liftScopeConstraints pm (Proxy :: Proxy valTyp)

rowStructureMismatch ::
    forall m key valTyp rowTyp.
    ( Recursive (Unify m) rowTyp
    , Unify m (RowExtend key valTyp rowTyp)
    ) =>
    (Tree (RowExtend key valTyp rowTyp) (UVar m) -> m (Tree (UVar m) rowTyp)) ->
    Tree (UTermBody (UVar m)) (RowExtend key valTyp rowTyp) ->
    Tree (UTermBody (UVar m)) (RowExtend key valTyp rowTyp) ->
    m (Tree (RowExtend key valTyp rowTyp) (UVar m))
rowStructureMismatch mkExtend
    (UTermBody c0 (RowExtend k0 v0 r0))
    (UTermBody c1 (RowExtend k1 v1 r1)) =
    withDict (recursive :: RecursiveDict (Unify m) rowTyp) $
    do
        restVar <- c0 \/ c1 & UUnbound & newVar binding
        _ <- RowExtend k0 v0 restVar & mkExtend >>= unify r1
        RowExtend k1 v1 restVar & mkExtend
            >>= unify r0
            <&> RowExtend k0 v0

inferRowExtend ::
    forall m val rowTyp key a.
    ( Infer m val
    , Unify m rowTyp
    , Unify m (RowExtend key (TypeAST val) rowTyp)
    ) =>
    (key -> TypeConstraints rowTyp -> TypeConstraints rowTyp) ->
    (Tree (UVar m) rowTyp -> m (Tree (UVar m) (TypeAST val))) ->
    Tree (RowExtend key val val) (Ann a) ->
    m
    ( Tree (UVar m) (RowExtend key (TypeAST val) rowTyp)
    , Tree (RowExtend key val val) (Ann (TypeOf m val, a))
    )
inferRowExtend forbid mkRowTyp (RowExtend k v r) =
    withDict (recursive :: RecursiveDict (Unify m) (TypeAST val)) $
    do
        vI <- inferNode v
        rI <- inferNode r
        restVar <-
            scopeConstraintsForType (Proxy :: Proxy rowTyp)
            >>= newVar binding . UUnbound . forbid k
        _ <- mkRowTyp restVar >>= unify (rI ^. nodeType)
        RowExtend k (vI ^. nodeType) restVar & newTerm
            <&> (, RowExtend k vI rI)
