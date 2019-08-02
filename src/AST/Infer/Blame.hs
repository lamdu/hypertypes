{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module AST.Infer.Blame
    ( Blame(..), blame
    ) where

import AST
import AST.Class.Foldable (sequenceLiftK2With_)
import AST.Class.NodesConstraint (KNodesConstraint)
import AST.Class.Traversable
import AST.Knot.Ann (annotationsWith)
import AST.Infer
import AST.Unify
import AST.Unify.Lookup
import AST.Unify.New
import AST.Unify.Occurs
import Control.Lens (mapped)
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
    ( MonadError err m
    , Recursively KFunctor exp
    , Recursively (Infer m) exp
    , Recursively (InferOfConstraint KApplicative) exp
    , Recursively (InferOfConstraint KTraversable) exp
    , Recursively (InferOfConstraint (KNodesConstraint (Recursively (Unify m)))) exp
    ) =>
    Tree (InferOf exp) (UVarOf m) ->
    Tree (Ann a) exp ->
    m (Tree (Ann (PrepAnn m a)) exp)
prepare typeFromAbove (Ann a x) =
    withDict (recursive @KFunctor @exp) $
    withDict (recursive @(Infer m) @exp) $
    withDict (recursive @(InferOfConstraint KApplicative) @exp) $
    withDict (recursive @(InferOfConstraint KTraversable) @exp) $
    withDict (recursive @(InferOfConstraint (KNodesConstraint (Recursively (Unify m)))) @exp) $
    inferBody
    (mapKWith
        (Proxy ::
            Proxy
            '[ Recursively KFunctor
            , Recursively (Infer m)
            , Recursively (InferOfConstraint KApplicative)
            , Recursively (InferOfConstraint KTraversable)
            , Recursively (InferOfConstraint (KNodesConstraint (Recursively (Unify m))))
            ])
        (\c ->
            do
                t <- sequencePureKWith (Proxy @'[Recursively (Unify m)]) newUnbound
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
            sequenceLiftK2With_
                (Proxy @'[Recursively (Unify m)])
                (unify <&> mapped . mapped .~ ()) typeFromAbove t
            traverseKWith_
                (Proxy @'[Recursively (Unify m)])
                occursCheck t
        & (`catchError` const (pure ()))
    , pFinalize =
        foldMapKWith
            (Proxy @'[Recursively (Unify m)])
            (\(Pair t0 t1) -> [(==) <$> (semiPruneLookup t0 <&> fst) <*> (semiPruneLookup t1 <&> fst)])
            (zipK typeFromAbove t)
        & sequenceA
        <&>
        \xs -> if and xs then Ok else TypeMismatch
    } xI

-- | Assign blame for type errors, given a prioritisation for the possible blame positions.
--
-- The expected `MonadError` behavior is that catching errors rolls back their state changes
-- (i.e `StateT s (Either e)` is ok but `EitherT e (State s)` is not)
blame ::
    forall priority err m exp a.
    ( Ord priority
    , MonadError err m
    , Recursively KNodes exp
    , Recursively KFunctor exp
    , Recursively KTraversable exp
    , Recursively (Infer m) exp
    , Recursively (InferOfConstraint KApplicative) exp
    , Recursively (InferOfConstraint KTraversable) exp
    , Recursively (InferOfConstraint (KNodesConstraint (Recursively (Unify m)))) exp
    ) =>
    (a -> priority) ->
    Tree (InferOf exp) (UVarOf m) ->
    Tree (Ann a) exp ->
    m (Tree (Ann (Blame, a)) exp)
blame order topLevelType e =
    do
        p <- prepare topLevelType e
        p ^.. annotationsWith prox Dict & sortOn (order . pAnn) & traverse_ pTryUnify
        annotationsWith prox Dict (\x -> pFinalize x <&> (, pAnn x)) p
    where
        prox = Proxy @'[Infer m, KTraversable]
