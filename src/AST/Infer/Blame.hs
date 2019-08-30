-- | Hindley-Milner type inference with ergonomic blame assignment.
--
-- 'blame' is a type-error blame assignment algorithm for languages with Hindley-Milner type inference,
-- but __/without generalization of intermediate terms/__.
-- This means that it is not suitable for languages with let-generalization.
-- 'AST.Term.Let.Let' is an example of a term that is not suitable for this algorithm.
--
-- With the contemporary knowledge that
-- ["Let Should Not Be Generalised"](https://www.microsoft.com/en-us/research/publication/let-should-not-be-generalised/),
-- as argued by luminaries such as Simon Peyton Jones,
-- optimistically this limitation shouldn't apply to new programming languages.
-- This blame assignment algorithm can also be used in a limited sense for existing languages,
-- which do have let-generalization, to provide better type errors
-- in specific definitions which don't happen to use generalizing terms.
--
-- [Lamdu](https://github.com/lamdu/lamdu) uses this algorithm for the "insist type" feature,
-- which moves around the blame for type mismatches.
--
-- Note: If a similar algorithm already existed somewhere,
-- I ([@yairchu](https://github.com/yairchu/)) would very much like to know!

{-# LANGUAGE FlexibleContexts, DefaultSignatures, TemplateHaskell, UndecidableInstances #-}

module AST.Infer.Blame
    ( blame
    , BTerm(..), InferOf', bAnn, bRes, bVal
    , Blamable(..)
    ) where

import AST
import AST.Class.Infer
import AST.Class.Recursive (recurseBoth)
import AST.Class.Unify (Unify, UVarOf)
import AST.TH.Internal.Instances (makeCommonInstances)
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

-- | Class implementing some primitives needed by the 'blame' algorithm
--
-- The 'blamableRecursive' method represents that 'Blamable' applies to all recursive child nodes.
-- It replaces context for 'Blamable' to avoid `UndecidableSuperClasses`.
class
    (RTraversable t, KTraversable (InferOf t)) =>
    Blamable t where

    -- | Create a new unbound infer result.
    --
    -- The type or values within should be unbound unification variables.
    inferOfNewUnbound ::
        Infer m t =>
        Proxy t ->
        m (Tree (InferOf t) (UVarOf m))

    -- | Unify the types/values in infer results
    inferOfUnify ::
        Infer m t =>
        Proxy t ->
        Tree (InferOf t) (UVarOf m) ->
        Tree (InferOf t) (UVarOf m) ->
        m ()

    -- | Check whether two infer results are the same
    inferOfMatches ::
        Infer m t =>
        Proxy t ->
        Tree (InferOf t) (UVarOf m) ->
        Tree (InferOf t) (UVarOf m) ->
        m Bool

    -- TODO: Putting documentation here causes duplication in the haddock documentation
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

-- | A type synonym to help 'BTerm' be more succinct
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
        resFromPosition <- inferOfNewUnbound (Proxy @exp)
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

-- | A 'Knot' for an inferred term with type mismatches - the output of 'blame'
data BTerm a v e = BTerm
    { _bAnn :: a
        -- ^ The node's original annotation as passed to 'blame'
    , _bRes :: Either (InferOf' e v, InferOf' e v) (InferOf' e v)
        -- ^ Either an infer result, or two conflicting results representing a type mismatch
    , _bVal :: Node e (BTerm a v)
        -- ^ The node's body and inferred child nodes
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
        match <- inferOfMatches (Proxy @exp) i0 i1
        let result
                | match = Right i0
                | otherwise = Left (i0, i1)
        traverseKWith (Proxy @(And Blamable (Infer m))) finalize x
            <&> BTerm a result

-- | Perform Hindley-Milner type inference with prioritised blame for type error,
-- given a prioritisation for the different nodes.
--
-- The purpose of the prioritisation is to place the errors in nodes where
-- the resulting errors will be easier to understand.
--
-- The expected `MonadError` behavior is that catching errors rolls back their state changes
-- (i.e @StateT s (Either e)@ is suitable but @EitherT e (State s)@ is not)
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
