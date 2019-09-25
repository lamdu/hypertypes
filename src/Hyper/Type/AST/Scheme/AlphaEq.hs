-- | Alpha-equality for schemes
{-# LANGUAGE FlexibleContexts #-}

module Hyper.Type.AST.Scheme.AlphaEq
    ( alphaEq
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))
import           Hyper
import           Hyper.Class.Has (HasChild(..))
import           Hyper.Class.ZipMatch (zipMatch_)
import           Hyper.Recurse (wrapM, (#>>))
import           Hyper.Type.AST.Scheme
import           Hyper.Unify
import           Hyper.Unify.New (newTerm)
import           Hyper.Unify.QuantifiedVar
import           Hyper.Unify.Term (UTerm(..), uBody)

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
    , HTraversable varTypes
    , HNodesConstraint varTypes (Unify m)
    , HasScheme varTypes m typ
    ) =>
    Tree Pure (Scheme varTypes typ) -> m (Tree (UVarOf m) typ)
schemeToRestrictedType (Pure (Scheme vars typ)) =
    do
        foralls <- traverseK (Proxy @(Unify m) #> makeQVarInstancesInScope) vars
        wrapM (Proxy @(HasScheme varTypes m) #>> schemeBodyToType foralls) typ

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
    zipMatch_ (Proxy @(Unify m) #> goUVar) (xt ^. uBody) (yt ^. uBody)
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
    ( HTraversable varTypes
    , HNodesConstraint varTypes (Unify m)
    , HasScheme varTypes m typ
    ) =>
    Tree Pure (Scheme varTypes typ) ->
    Tree Pure (Scheme varTypes typ) ->
    m ()
alphaEq s0 s1 =
    do
        t0 <- schemeToRestrictedType s0
        t1 <- schemeToRestrictedType s1
        goUVar t0 t1
