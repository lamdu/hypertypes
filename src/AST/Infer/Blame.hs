{-# LANGUAGE FlexibleContexts, DefaultSignatures #-}

module AST.Infer.Blame
    ( Blamable(..), Blame(..), blame
    ) where

import AST
import AST.Class.Foldable (sequenceLiftK2With_)
import AST.Class.Traversable
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

class (Infer m t, KApplicative (InferOf t)) => Blamable m t where
    blamableRecursive :: Proxy m -> Proxy t -> Dict (NodesConstraint t (Blamable m))
    {-# INLINE blamableRecursive #-}
    default blamableRecursive ::
        NodesConstraint t (Blamable m) =>
        Proxy m -> Proxy t -> Dict (NodesConstraint t (Blamable m))
    blamableRecursive _ _ = Dict

data Blame = Ok | TypeMismatch

data PrepAnn m a = PrepAnn
    { pAnn :: a
    , pTryUnify :: m ()
    , pFinalize :: m Blame
    }

prepare ::
    forall err m exp a.
    ( MonadError err m
    , Blamable m exp
    ) =>
    Tree (InferOf exp) (UVarOf m) ->
    Tree (Ann a) exp ->
    m (Tree (Ann (PrepAnn m a)) exp)
prepare typeFromAbove (Ann a x) =
    withDict (traversableInferOf (Proxy @exp)) $
    withDict (inferredUnify (Proxy @m) (Proxy @exp)) $
    withDict (blamableRecursive (Proxy @m) (Proxy @exp)) $
    inferBody
    (mapKWith (Proxy @(Blamable m))
        (\c ->
            let p :: Tree (Ann a) k -> Proxy k
                p _ = Proxy
            in
            withDict (inferredUnify (Proxy @m) (p c)) $
            withDict (traversableInferOf (p c)) $
            do
                t <- sequencePureKWith (Proxy @(Unify m)) newUnbound
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
            sequenceLiftK2With_ (Proxy @(Unify m))
                (unify <&> mapped . mapped .~ ()) typeFromAbove t
            traverseKWith_ (Proxy @(Unify m)) occursCheck t
        & (`catchError` const (pure ()))
    , pFinalize =
        foldMapKWith (Proxy @(Unify m))
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
    , RTraversable exp
    , Blamable m exp
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
