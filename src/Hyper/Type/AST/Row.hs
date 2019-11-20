-- | Row types

{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts, TemplateHaskell #-}

module Hyper.Type.AST.Row
    ( RowConstraints(..), RowKey
    , RowExtend(..), eKey, eVal, eRest, W_RowExtend(..)
    , FlatRowExtends(..), freExtends, freRest, W_FlatRowExtends(..)
    , flattenRow, flattenRowExtend, unflattenRow
    , verifyRowExtendConstraints, rowExtendStructureMismatch
    , rowElementInfer
    ) where

import           Control.DeepSeq (NFData)
import           Control.Lens (Prism', Lens', makeLenses, contains)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (foldM)
import           Data.Binary (Binary)
import           Data.Foldable (sequenceA_)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           Data.Set (Set)
import           GHC.Generics (Generic)
import           Generics.Constraints (Constraints, makeDerivings, makeInstances)
import           Hyper
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Unify
import           Hyper.Unify.Lookup (semiPruneLookup)
import           Hyper.Unify.New (newTerm, newUnbound)
import           Hyper.Unify.Term (UTerm(..), _UTerm, uBody)
import           Text.Show.Combinators ((@|), showCon)

import           Prelude.Compat

class
    (Ord (RowConstraintsKey constraints), TypeConstraints constraints) =>
    RowConstraints constraints where

    type RowConstraintsKey constraints
    forbidden :: Lens' constraints (Set (RowConstraintsKey constraints))

type RowKey typ = RowConstraintsKey (TypeConstraintsOf typ)

-- | Row-extend primitive for use in both value-level and type-level
data RowExtend key val rest h = RowExtend
    { _eKey :: key
    , _eVal :: h # val
    , _eRest :: h # rest
    } deriving Generic

data FlatRowExtends key val rest h = FlatRowExtends
    { _freExtends :: Map key (h # val)
    , _freRest :: h # rest
    } deriving Generic

makeLenses ''RowExtend
makeLenses ''FlatRowExtends
makeCommonInstances [''FlatRowExtends]
makeZipMatch ''RowExtend
makeHContext ''RowExtend
makeHTraversableApplyAndBases ''RowExtend
makeHTraversableApplyAndBases ''FlatRowExtends
makeDerivings [''Eq, ''Ord] [''RowExtend]
makeInstances [''Binary, ''NFData] [''RowExtend]

instance
    Constraints (RowExtend key val rest h) Show =>
    Show (RowExtend key val rest h) where
    showsPrec p (RowExtend h v r) = (showCon "RowExtend" @| h @| v @| r) p

{-# INLINE flattenRowExtend #-}
flattenRowExtend ::
    (Ord key, Monad m) =>
    (Tree v rest -> m (Maybe (Tree (RowExtend key val rest) v))) ->
    Tree (RowExtend key val rest) v ->
    m (Tree (FlatRowExtends key val rest) v)
flattenRowExtend nextExtend (RowExtend h v rest) =
    flattenRow nextExtend rest
    <&> freExtends %~ Map.unionWith (error "Colliding keys") (Map.singleton h v)

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

{-# INLINE verifyRowExtendConstraints #-}
verifyRowExtendConstraints ::
    RowConstraints (TypeConstraintsOf rowTyp) =>
    (TypeConstraintsOf rowTyp -> TypeConstraintsOf valTyp) ->
    TypeConstraintsOf rowTyp ->
    Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) h ->
    Maybe (Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) (WithConstraint h))
verifyRowExtendConstraints toChildC c (RowExtend h v rest)
    | c ^. forbidden . contains h = Nothing
    | otherwise =
        RowExtend h
        (WithConstraint (c & forbidden .~ mempty & toChildC) v)
        (WithConstraint (c & forbidden . contains h .~ True) rest)
        & Just

{-# INLINE rowExtendStructureMismatch #-}
rowExtendStructureMismatch ::
    Ord key =>
    ( Unify m rowTyp
    , Unify m valTyp
    ) =>
    (forall c. Unify m c => Tree (UVarOf m) c -> Tree (UVarOf m) c -> m (Tree (UVarOf m) c)) ->
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
    forall m valTyp rowTyp.
    ( Unify m valTyp
    , Unify m rowTyp
    , RowConstraints (TypeConstraintsOf rowTyp)
    ) =>
    (Tree (RowExtend (RowKey rowTyp) valTyp rowTyp) (UVarOf m) -> Tree rowTyp (UVarOf m)) ->
    RowKey rowTyp ->
    m (Tree (UVarOf m) valTyp, Tree (UVarOf m) rowTyp)
rowElementInfer extendToRow h =
    do
        restVar <-
            scopeConstraints (Proxy @rowTyp)
            >>= newVar binding . UUnbound . (forbidden . contains h .~ True)
        part <- newUnbound
        whole <- RowExtend h part restVar & extendToRow & newTerm
        pure (part, whole)
