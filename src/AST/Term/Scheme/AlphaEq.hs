-- | Alpha-equality for schemes
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module AST.Term.Scheme.AlphaEq
    ( alphaEq
    ) where

import           AST
import           AST.Class.Has (HasChild(..))
import           AST.Class.Recursive (wrapMDeprecated)
import           AST.Class.ZipMatch (zipMatchWith_)
import           AST.Term.Scheme
import           AST.Unify
import           AST.Unify.New (newTerm)
import           AST.Unify.QuantifiedVar
import           AST.Unify.Term (UTerm(..), uBody)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

makeQVarInstancesInScope ::
    Unify m typ =>
    Tree QVars typ -> m (Tree (QVarInstances (UVarOf m)) typ)
makeQVarInstancesInScope (QVars foralls) =
    traverse makeSkolem foralls <&> QVarInstances
    where
        makeSkolem c = scopeConstraints >>= newVar binding . USkolem . (c <>)

schemeBodyToType ::
    (Unify m typ, HasChild varTypes typ, Ord (QVar typ)) =>
    Tree varTypes (QVarInstances (UVarOf m)) -> Tree typ (UVarOf m) -> m (Tree (UVarOf m) typ)
schemeBodyToType foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Nothing -> newTerm x
    Just r -> pure r
    where
        getForAll v = foralls ^? getChild . _QVarInstances . Lens.ix v

schemeToRestrictedType ::
    forall m varTypes typ.
    ( Monad m
    , KTraversable varTypes
    , NodesConstraint varTypes $ Unify m
    , RLiftConstraints typ '[Unify m, HasChild varTypes, QVarHasInstance Ord]
    ) =>
    Tree Pure (Scheme varTypes typ) -> m (Tree (UVarOf m) typ)
schemeToRestrictedType (MkPure (Scheme vars typ)) =
    do
        foralls <- traverseKWith (Proxy @'[Unify m]) makeQVarInstancesInScope vars
        wrapMDeprecated
            (Proxy @'[Unify m, HasChild varTypes, QVarHasInstance Ord])
            Dict (schemeBodyToType foralls) typ

goUTerm ::
    forall m t.
    Unify m t =>
    Tree (UVarOf m) t -> Tree (UTerm (UVarOf m)) t ->
    Tree (UVarOf m) t -> Tree (UTerm (UVarOf m)) t ->
    m ()
goUTerm xv USkolem{} yv USkolem{} =
    do
        bindVar binding xv (UInstantiated yv)
        bindVar binding yv (UInstantiated xv)
goUTerm xv (UInstantiated xt) yv (UInstantiated yt)
    | xv == yt && yv == xt = pure ()
    | otherwise = unifyError (SkolemEscape xv)
goUTerm xv USkolem{} yv UUnbound{} = bindVar binding yv (UToVar xv)
goUTerm xv UUnbound{} yv USkolem{} = bindVar binding xv (UToVar yv)
goUTerm _ (UToVar xv) yv yu =
    do
        xu <- lookupVar binding xv
        goUTerm xv xu yv yu
goUTerm xv xu _ (UToVar yv) =
    do
        yu <- lookupVar binding yv
        goUTerm xv xu yv yu
goUTerm xv USkolem{} yv _ = unifyError (SkolemUnified xv yv)
goUTerm xv _ yv USkolem{} = unifyError (SkolemUnified yv xv)
goUTerm xv UUnbound{} yv yu = goUTerm xv yu yv yu -- Term created in structure mismatch
goUTerm xv xu yv UUnbound{} = goUTerm xv xu yv xu -- Term created in structure mismatch
goUTerm _ (UTerm xt) _ (UTerm yt) =
    withDict (unifyRecursive (Proxy @m) (Proxy @t)) $
    zipMatchWith_ (Proxy @'[Unify m]) goUVar (xt ^. uBody) (yt ^. uBody)
    & fromMaybe (structureMismatch (\x y -> x <$ goUVar x y) xt yt)
goUTerm _ _ _ _ = error "unexpected state at alpha-eq"

goUVar ::
    Unify m t =>
    Tree (UVarOf m) t -> Tree (UVarOf m) t -> m ()
goUVar xv yv =
    do
        xu <- lookupVar binding xv
        yu <- lookupVar binding yv
        goUTerm xv xu yv yu

-- Check for alpha equality. Raises a `unifyError` when mismatches.
alphaEq ::
    ( KTraversable varTypes
    , NodesConstraint varTypes $ Unify m
    , Recursively KNodes typ
    , Recursively (Unify m) typ
    , Recursively (HasChild varTypes) typ
    , Recursively (QVarHasInstance Ord) typ
    ) =>
    Tree Pure (Scheme varTypes typ) ->
    Tree Pure (Scheme varTypes typ) ->
    m ()
alphaEq s0 s1 =
    do
        t0 <- schemeToRestrictedType s0
        t1 <- schemeToRestrictedType s1
        goUVar t0 t1
