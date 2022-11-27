{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Row types
module Hyper.Syntax.Row
    ( RowConstraints (..)
    , RowKey
    , RowExtend (..)
    , eKey
    , eVal
    , eRest
    , W_RowExtend (..)
    , FlatRowExtends (..)
    , freExtends
    , freRest
    , W_FlatRowExtends (..)
    , MorphWitness (..)
    , flattenRow
    , flattenRowExtend
    , unflattenRow
    , verifyRowExtendConstraints
    , rowExtendStructureMismatch
    , rowElementInfer
    ) where

import Control.Lens (Lens', Prism', contains)
import qualified Control.Lens as Lens
import Control.Monad (foldM)
import qualified Data.Map as Map
import Generics.Constraints (Constraints, makeDerivings, makeInstances)
import Hyper
import Hyper.Unify
import Hyper.Unify.New (newTerm, newUnbound)
import Hyper.Unify.Term (UTerm (..), UTermBody (..), uBody, _UTerm)
import Text.Show.Combinators (showCon, (@|))

import Hyper.Internal.Prelude

class
    (Ord (RowConstraintsKey constraints), TypeConstraints constraints) =>
    RowConstraints constraints
    where
    type RowConstraintsKey constraints
    forbidden :: Lens' constraints (Set (RowConstraintsKey constraints))

type RowKey typ = RowConstraintsKey (TypeConstraintsOf typ)

-- | Row-extend primitive for use in both value-level and type-level
data RowExtend key val rest h = RowExtend
    { _eKey :: key
    , _eVal :: h :# val
    , _eRest :: h :# rest
    }
    deriving (Generic)

data FlatRowExtends key val rest h = FlatRowExtends
    { _freExtends :: Map key (h :# val)
    , _freRest :: h :# rest
    }
    deriving (Generic)

makeLenses ''RowExtend
makeLenses ''FlatRowExtends
makeCommonInstances [''FlatRowExtends]
makeZipMatch ''RowExtend
makeHContext ''RowExtend
makeHMorph ''RowExtend
makeHTraversableApplyAndBases ''RowExtend
makeHTraversableApplyAndBases ''FlatRowExtends
makeDerivings [''Eq, ''Ord] [''RowExtend]
makeInstances [''Binary, ''NFData] [''RowExtend]

instance
    Constraints (RowExtend key val rest h) Show =>
    Show (RowExtend key val rest h)
    where
    showsPrec p (RowExtend h v r) = (showCon "RowExtend" @| h @| v @| r) p

{-# INLINE flattenRowExtend #-}
flattenRowExtend ::
    (Ord key, Monad m) =>
    (v # rest -> m (Maybe (RowExtend key val rest # v))) ->
    RowExtend key val rest # v ->
    m (FlatRowExtends key val rest # v)
flattenRowExtend nextExtend (RowExtend h v rest) =
    flattenRow nextExtend rest
        <&> freExtends %~ Map.unionWith (error "Colliding keys") (Map.singleton h v)

{-# INLINE flattenRow #-}
flattenRow ::
    (Ord key, Monad m) =>
    (v # rest -> m (Maybe (RowExtend key val rest # v))) ->
    v # rest ->
    m (FlatRowExtends key val rest # v)
flattenRow nextExtend x =
    nextExtend x
        >>= maybe (pure (FlatRowExtends mempty x)) (flattenRowExtend nextExtend)

{-# INLINE unflattenRow #-}
unflattenRow ::
    Monad m =>
    (RowExtend key val rest # v -> m (v # rest)) ->
    FlatRowExtends key val rest # v ->
    m (v # rest)
unflattenRow mkExtend (FlatRowExtends fields rest) =
    fields ^@.. Lens.itraversed & foldM f rest
    where
        f acc (key, val) = RowExtend key val acc & mkExtend

-- Helpers for Unify instances of type-level RowExtends:

{-# INLINE verifyRowExtendConstraints #-}
verifyRowExtendConstraints ::
    RowConstraints (TypeConstraintsOf rowTyp) =>
    (TypeConstraintsOf rowTyp -> TypeConstraintsOf valTyp) ->
    TypeConstraintsOf rowTyp ->
    RowExtend (RowKey rowTyp) valTyp rowTyp # h ->
    Maybe (RowExtend (RowKey rowTyp) valTyp rowTyp # WithConstraint h)
verifyRowExtendConstraints toChildC c (RowExtend h v rest)
    | c ^. forbidden . contains h = Nothing
    | otherwise =
        RowExtend
            h
            (WithConstraint (c & forbidden .~ mempty & toChildC) v)
            (WithConstraint (c & forbidden . contains h .~ True) rest)
            & Just

{-# INLINE rowExtendStructureMismatch #-}
rowExtendStructureMismatch ::
    Ord key =>
    ( Unify m rowTyp
    , Unify m valTyp
    ) =>
    (forall c. Unify m c => UVarOf m # c -> UVarOf m # c -> m (UVarOf m # c)) ->
    Prism' (rowTyp # UVarOf m) (RowExtend key valTyp rowTyp # UVarOf m) ->
    RowExtend key valTyp rowTyp # UVarOf m ->
    RowExtend key valTyp rowTyp # UVarOf m ->
    m ()
rowExtendStructureMismatch match extend r0 r1 =
    do
        flat0 <- flattenRowExtend nextExtend r0
        flat1 <- flattenRowExtend nextExtend r1
        Map.intersectionWith match (flat0 ^. freExtends) (flat1 ^. freExtends)
            & sequenceA_
        restVar <- UUnbound mempty & newVar binding
        let side x y =
                unflattenRow
                    mkExtend
                    FlatRowExtends
                        { _freExtends =
                            (x ^. freExtends) `Map.difference` (y ^. freExtends)
                        , _freRest = restVar
                        }
                    >>= match (y ^. freRest)
        _ <- side flat0 flat1
        _ <- side flat1 flat0
        pure ()
    where
        mkExtend ext = UTermBody mempty (extend # ext) & UTerm & newVar binding
        nextExtend v = semiPruneLookup v <&> (^? Lens._2 . _UTerm . uBody . extend)

-- Helper for infering row usages of a row element,
-- such as getting a field from a record or injecting into a sum type.
-- Returns a unification variable for the element and for the whole row.
{-# INLINE rowElementInfer #-}
rowElementInfer ::
    forall m valTyp rowTyp.
    ( UnifyGen m valTyp
    , UnifyGen m rowTyp
    , RowConstraints (TypeConstraintsOf rowTyp)
    ) =>
    (RowExtend (RowKey rowTyp) valTyp rowTyp # UVarOf m -> rowTyp # UVarOf m) ->
    RowKey rowTyp ->
    m (UVarOf m # valTyp, UVarOf m # rowTyp)
rowElementInfer extendToRow h =
    do
        restVar <-
            scopeConstraints (Proxy @rowTyp)
                >>= newVar binding . UUnbound . (forbidden . contains h .~ True)
        part <- newUnbound
        whole <- RowExtend h part restVar & extendToRow & newTerm
        pure (part, whole)
