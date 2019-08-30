{-# LANGUAGE FlexibleContexts, DefaultSignatures, TemplateHaskell, UndecidableInstances #-}

module AST.Infer.Blame
    ( blame
    , BTerm(..), bAnn, bRes, bVal
    , Blamable(..)
    ) where

import AST
import AST.Class.Recursive (recurseBoth)
import AST.Infer
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.Unify
import AST.Unify.Occurs (occursCheck)
import Control.Lens (makeLenses)
import Control.Lens.Operators
import Control.Monad.Except (MonadError(..))
import Data.Constraint (Dict(..), withDict)
import Data.Foldable (traverse_)
import Data.List (sortOn)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

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

    inferOfIsUnified ::
        Infer m t =>
        Proxy t ->
        Tree (InferOf t) (UVarOf m) ->
        Tree (InferOf t) (UVarOf m) ->
        m Bool

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

type InferOf' e v = Tree (InferOf (RunKnot e)) v

-- Internal Knot for the blame algorithm
data PTerm a v e = PTerm
    { pAnn :: a
    , pInferResultFromPos :: InferOf' e v
    , pInferResultFromSelf :: InferOf' e v
    , pBody :: Node e (PTerm a v)
    }

prepare ::
    forall m exp a.
    (Blamable exp, Infer m exp) =>
    Tree (Ann a) exp ->
    m (Tree (PTerm a (UVarOf m)) exp)
prepare (Ann a x) =
    withDict (recurseBoth (Proxy @(And Blamable (Infer m) exp))) $
    do
        resFromPosition <- inferOfNew (Proxy @exp)
        (xI, r) <-
            mapKWith (Proxy @(And Blamable (Infer m)))
            (InferChild . fmap (\t -> InferredChild t (pInferResultFromPos t)) . prepare)
            x
            & inferBody
        pure PTerm
            { pAnn = a
            , pInferResultFromPos = resFromPosition
            , pInferResultFromSelf = r
            , pBody = xI
            }

tryUnify ::
    forall exp m.
    (Blamable exp, Infer m exp) =>
    Proxy exp ->
    Tree (InferOf exp) (UVarOf m) ->
    Tree (InferOf exp) (UVarOf m) ->
    m ()
tryUnify p i0 i1 =
    withDict (inferContext (Proxy @m) p) $
    do
        inferOfUnify p i0 i1
        traverseKWith_ (Proxy @(Unify m)) occursCheck i0

toUnifies ::
    forall a m exp.
    (Blamable exp, Infer m exp) =>
    Tree (PTerm a (UVarOf m)) exp ->
    Tree (Ann (a, m ())) exp
toUnifies (PTerm a i0 i1 b) =
    withDict (recurseBoth (Proxy @(And Blamable (Infer m) exp))) $
    mapKWith (Proxy @(And Blamable (Infer m))) toUnifies b
    & Ann (a, tryUnify (Proxy @exp) i0 i1)

data BTerm a v e = BTerm
    { _bAnn :: a
    , _bRes :: Either (InferOf' e v, InferOf' e v) (InferOf' e v)
    , _bVal :: Node e (BTerm a v)
    } deriving Generic
makeLenses ''BTerm
makeCommonInstances [''BTerm]

finalize ::
    forall a m exp.
    (Blamable exp, Infer m exp) =>
    Tree (PTerm a (UVarOf m)) exp ->
    m (Tree (BTerm a (UVarOf m)) exp)
finalize (PTerm a i0 i1 x) =
    withDict (recurseBoth (Proxy @(And Blamable (Infer m) exp))) $
    do
        isUnified <- inferOfIsUnified (Proxy @exp) i0 i1
        let result
                | isUnified = Right i0
                | otherwise = Left (i0, i1)
        traverseKWith (Proxy @(And Blamable (Infer m))) finalize x
            <&> BTerm a result

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
    Tree (Ann a) exp ->
    m (Tree (BTerm a (UVarOf m)) exp)
blame order e =
    do
        p <- prepare e
        toUnifies p ^.. annotations & sortOn (order . fst) & traverse_ snd
        finalize p
