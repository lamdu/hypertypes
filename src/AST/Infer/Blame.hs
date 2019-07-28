{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, ScopedTypeVariables, TupleSections #-}
{-# LANGUAGE DataKinds #-}

module AST.Infer.Blame
    ( Blame(..), blame
    ) where

import AST
import AST.Knot.Ann (annotationsWith)
import AST.Infer
import AST.Unify
import AST.Unify.Lookup
import AST.Unify.New
import AST.Unify.Occurs
import Control.Lens.Operators
import Control.Monad.Except (MonadError(..))
import Data.Constraint
import Data.Foldable (traverse_)
import Data.List (sortOn)
import Data.Proxy

import Prelude.Compat

data Blame = Ok | TypeMismatch

data PrepAnn m a = PrepAnn
    { pAnn :: a
    , pTryUnify :: m ()
    , pFinalize :: m Blame
    }

prepare ::
    forall err m exp a.
    (MonadError err m, Recursively (Infer m) exp, Recursively KFunctor exp) =>
    Tree (UVarOf m) (TypeOf exp) ->
    Tree (Ann a) exp ->
    m (Tree (Ann (PrepAnn m a)) exp)
prepare typeFromAbove (Ann a x) =
    withDict (recursive :: RecursiveDict exp (Infer m)) $
    withDict (recursive :: RecursiveDict exp KFunctor) $
    inferBody
    (mapKWith (Proxy :: Proxy '[Recursively (Infer m), Recursively KFunctor])
        (\c ->
            do
                t <- newUnbound
                prepare t c <&> (`InferredChild` t)
            & InferChild
        )
        x)
    <&>
    \(InferRes xI t) ->
    Ann PrepAnn
    { pAnn = a
    , pTryUnify =
        do
            _ <- unify typeFromAbove t
            occursCheck t
        & (`catchError` const (pure ()))
    , pFinalize =
        do
            (t0, _) <- semiPruneLookup typeFromAbove
            (t1, _) <- semiPruneLookup t
            if t0 == t1
                then pure Ok
                else pure TypeMismatch
    } xI

-- | Assign blame for type errors, given a prioritisation for the possible blame positions.
--
-- The expected `MonadError` behavior is that catching errors rolls back their state changes
-- (i.e `StateT s (Either e)` is ok but `EitherT e (State s)` is not)
blame ::
    forall priority err m exp a.
    ( Ord priority
    , MonadError err m
    , Recursively (Infer m) exp
    , Recursively KTraversable exp
    , Recursively KFunctor exp
    , Recursively HasNodes exp
    ) =>
    (a -> priority) ->
    Tree (UVarOf m) (TypeOf exp) ->
    Tree (Ann a) exp ->
    m (Tree (Ann (Blame, a)) exp)
blame order topLevelType e =
    do
        p <- prepare topLevelType e
        p ^.. annotationsWith prox Dict & sortOn (order . pAnn) & traverse_ pTryUnify
        annotationsWith prox Dict (\x -> pFinalize x <&> (, pAnn x)) p
    where
        prox :: Proxy '[Infer m, KTraversable]
        prox = Proxy
