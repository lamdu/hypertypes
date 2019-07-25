{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module AST.Term.Row
    ( RowConstraints(..), RowKey
    , RowExtend(..), eKey, eVal, eRest
    , FlatRowExtends(..), freExtends, freRest
    , flattenRow, flattenRowExtend, unflattenRow
    , applyRowExtendConstraints, rowExtendStructureMismatch
    , rowElementInfer
    ) where

import           AST
import           AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           AST.Combinator.Pair (Pair)
import           AST.Unify (TypeConstraints(..), HasTypeConstraints(..), MonadScopeConstraints(..))
import           AST.Unify.Lookup (semiPruneLookup)
import           AST.Unify.New (newTerm, newUnbound)
import           AST.Unify.Term (UTerm(..), _UTerm, uBody)
import           Control.DeepSeq (NFData)
import           Control.Lens (Prism', Lens', makeLenses, contains)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (when, foldM)
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           Data.Foldable (sequenceA_)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           Data.Set (Set)
import           GHC.Generics (Generic)
import           Text.Show.Combinators ((@|), showCon)

import           Prelude.Compat

class
    (Ord (RowConstraintsKey constraints), TypeConstraints constraints) =>
    RowConstraints constraints where

    type RowConstraintsKey constraints
    forbidden :: Lens' constraints (Set (RowConstraintsKey constraints))

type RowKey typ = RowConstraintsKey (TypeConstraintsOf typ)

-- | Row-extend primitive for use in both value-level and type-level
data RowExtend key val rest k = RowExtend
    { _eKey :: key
    , _eVal :: Node k val
    , _eRest :: Node k rest
    } deriving Generic

data FlatRowExtends key val rest k = FlatRowExtends
    { _freExtends :: Map key (Node k val)
    , _freRest :: Node k rest
    } deriving Generic

instance HasNodeTypes (RowExtend k v r) where
    type NodeTypesOf (RowExtend k v r) = Pair v r
instance HasNodeTypes (FlatRowExtends k v r) where
    type NodeTypesOf (FlatRowExtends k v r) = Pair v r

makeLenses ''RowExtend
makeLenses ''FlatRowExtends
makeZipMatch ''RowExtend
makeKTraversableAndBases ''RowExtend
makeKTraversableAndBases ''FlatRowExtends

instance
    RecursiveConstraint (RowExtend key val rest) constraint =>
    Recursive constraint (RowExtend key val rest)

type Deps c key val rest k = ((c key, c (Node k val), c (Node k rest)) :: Constraint)

instance Deps Show key val rest k => Show (RowExtend key val rest k) where
    showsPrec p (RowExtend k v r) = (showCon "RowExtend" @| k @| v @| r) p

{-# INLINE flattenRowExtend #-}
flattenRowExtend ::
    (Ord key, Monad m) =>
    (Tree v rest -> m (Maybe (Tree (RowExtend key val rest) v))) ->
    Tree (RowExtend key val rest) v ->
    m (Tree (FlatRowExtends key val rest) v)
flattenRowExtend nextExtend (RowExtend k v rest) =
    flattenRow nextExtend rest
    <&> freExtends %~ Map.unionWith (error "Colliding keys") (Map.singleton k v)

{-# INLINE flattenRow #-}
flattenRow ::
    (Ord key, Monad m) =>
    (Tree v rest -> m (Maybe (Tree (RowExtend key val rest) v))) ->
    Tree v rest ->
    m (Tree (FlatRowExtends key val rest) v)
flattenRow nextExtend x =
    nextExtend x
    >>= maybe (pure (FlatRowExtends mempty x)) (flattenRowExtend nextExtend)

{-# INLINE unflattenRow #-}
unflattenRow ::
    Monad m =>
    (Tree (RowExtend key val rest) v -> m (Tree v rest)) ->
    Tree (FlatRowExtends key val rest) v -> m (Tree v rest)
unflattenRow mkExtend (FlatRowExtends fields rest) =
    Map.toList fields & foldM f rest
    where
        f acc (key, val) = RowExtend key val acc & mkExtend

-- Helpers for Unify instances of type-level RowExtends:

{-# INLINE applyRowExtendConstraints #-}
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

{-# INLINE rowExtendStructureMismatch #-}
rowExtendStructureMismatch ::
    Ord key =>
    ( Recursive (Unify m) rowTyp
    , Recursive (Unify m) valTyp
    ) =>
    (forall c. Recursive (Unify m) c => Tree (UVarOf m) c -> Tree (UVarOf m) c -> m (Tree (UVarOf m) c)) ->
    Prism' (Tree rowTyp (UVarOf m))
        (Tree (RowExtend key valTyp rowTyp) (UVarOf m)) ->
    (TypeConstraintsOf rowTyp, Tree (RowExtend key valTyp rowTyp) (UVarOf m)) ->
    (TypeConstraintsOf rowTyp, Tree (RowExtend key valTyp rowTyp) (UVarOf m)) ->
    m ()
rowExtendStructureMismatch match extend (c0, r0) (c1, r1) =
    do
        flat0 <- flattenRowExtend nextExtend r0
        flat1 <- flattenRowExtend nextExtend r1
        Map.intersectionWith match (flat0 ^. freExtends) (flat1 ^. freExtends)
            & sequenceA_
        restVar <- c0 <> c1 & UUnbound & newVar binding
        let side x y =
                unflattenRow mkExtend FlatRowExtends
                { _freExtends =
                  (x ^. freExtends) `Map.difference` (y ^. freExtends)
                , _freRest = restVar
                } >>= match (y ^. freRest)
        _ <- side flat0 flat1
        _ <- side flat1 flat0
        pure ()
    where
        mkExtend ext = extend # ext & newTerm
        nextExtend v = semiPruneLookup v <&> (^? Lens._2 . _UTerm . uBody . extend)

-- Helper for infering row usages of a row element,
-- such as getting a field from a record or injecting into a sum type.
-- Returns a unification variable for the element and for the whole row.
{-# INLINE rowElementInfer #-}
rowElementInfer ::
    ( Unify m valTyp
    , Unify m rowTyp
    , RowConstraints (TypeConstraintsOf rowTyp)
    ) =>
    (Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) (UVarOf m) -> Tree rowTyp (UVarOf m)) ->
    RowKey rowTyp ->
    m (Tree (UVarOf m) valTyp, Tree (UVarOf m) rowTyp)
rowElementInfer extendToRow k =
    do
        restVar <-
            scopeConstraints
            >>= newVar binding . UUnbound . (forbidden . contains k .~ True)
        part <- newUnbound
        whole <- RowExtend k part restVar & extendToRow & newTerm
        pure (part, whole)

deriving instance Deps Eq   key val rest k => Eq   (RowExtend key val rest k)
deriving instance Deps Ord  key val rest k => Ord  (RowExtend key val rest k)
instance Deps Binary key val rest k => Binary (RowExtend key val rest k)
instance Deps NFData key val rest k => NFData (RowExtend key val rest k)

deriving instance Deps Eq   key val rest k => Eq   (FlatRowExtends key val rest k)
deriving instance Deps Ord  key val rest k => Ord  (FlatRowExtends key val rest k)
deriving instance Deps Show key val rest k => Show (FlatRowExtends key val rest k)
instance Deps Binary key val rest k => Binary (FlatRowExtends key val rest k)
instance Deps NFData key val rest k => NFData (FlatRowExtends key val rest k)
