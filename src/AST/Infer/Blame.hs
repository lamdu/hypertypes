{-# LANGUAGE FlexibleContexts, DefaultSignatures #-}

module AST.Infer.Blame
    ( Blamable(..), Blame(..), blame
    ) where

import AST
import AST.Class.Recursive
import AST.Infer
import AST.Unify
import AST.Unify.Occurs
import Control.Lens.Operators
import Control.Monad.Except (MonadError(..))
import Data.Constraint
import Data.Foldable (traverse_)
import Data.List (sortOn)
import Data.Proxy

import Prelude.Compat

data Blame = Ok | TypeMismatch

class
    (RTraversable t, KTraversable (InferOf t)) =>
    Blamable t where

    inferOfNew ::
        Infer m t =>
        Proxy t ->
        m (Tree (InferOf t) (UVarOf m))

    inferOfUnify ::
        Infer m t =>
        Proxy t ->
        Tree (InferOf t) (UVarOf m) ->
        Tree (InferOf t) (UVarOf m) ->
        m ()

    inferOfUnified ::
        Infer m t =>
        Proxy t ->
        Tree (InferOf t) (UVarOf m) ->
        Tree (InferOf t) (UVarOf m) ->
        m Blame

    blamableRecursive :: Proxy t -> Dict (NodesConstraint t Blamable)
    {-# INLINE blamableRecursive #-}
    default blamableRecursive ::
        NodesConstraint t Blamable =>
        Proxy t -> Dict (NodesConstraint t Blamable)
    blamableRecursive _ = Dict

instance Recursive Blamable where
    recurse =
        blamableRecursive . p
        where
            p :: Proxy (Blamable k) -> Proxy k
            p _ = Proxy

data PrepAnn m a = PrepAnn
    { pAnn :: a
    , pTryUnify :: m ()
    , pFinalize :: m Blame
    }

prepare ::
    forall err m exp a.
    ( MonadError err m
    , Blamable exp
    , Infer m exp
    ) =>
    Tree (InferOf exp) (UVarOf m) ->
    Tree (Ann a) exp ->
    m (Tree (Ann (PrepAnn m a)) exp)
prepare typeFromAbove (Ann a x) =
    withDict (inferContext (Proxy @m) (Proxy @exp)) $
    withDict (recurseBoth (Proxy @(And (Infer m) Blamable exp))) $
    inferBody
    (mapKWith (Proxy @(And (Infer m) Blamable))
        (\c ->
            let mkP :: Tree (Ann a) k -> Proxy k
                mkP _ = Proxy
                p = mkP c
            in
            withDict (inferContext (Proxy @m) p) $
            do
                t <- inferOfNew p
                prepare t c <&> (`InferredChild` t)
            & InferChild
        )
        x)
    <&>
    \(xI, t) ->
    Ann PrepAnn
    { pAnn = a
    , pTryUnify =
        do
            inferOfUnify (Proxy @exp) typeFromAbove t
            traverseKWith_ (Proxy @(Unify m)) occursCheck t
        & (`catchError` const (pure ()))
    , pFinalize = inferOfUnified (Proxy @exp) typeFromAbove t
    } xI

-- | Assign blame for type errors, given a prioritisation for the possible blame positions.
--
-- The expected `MonadError` behavior is that catching errors rolls back their state changes
-- (i.e `StateT s (Either e)` is ok but `EitherT e (State s)` is not)
blame ::
    forall priority err m exp a.
    ( Ord priority
    , MonadError err m
    , Blamable exp
    , Infer m exp
    ) =>
    (a -> priority) ->
    Tree (InferOf exp) (UVarOf m) ->
    Tree (Ann a) exp ->
    m (Tree (Ann (Blame, a)) exp)
blame order topLevelType e =
    do
        p <- prepare topLevelType e
        p ^.. annotations & sortOn (order . pAnn) & traverse_ pTryUnify
        annotations (\x -> pFinalize x <&> (, pAnn x)) p
