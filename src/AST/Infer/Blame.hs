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
-- The algorithm is pretty simple:
--
-- * Invoke all the 'inferBody' calls as 'AST.Infer.infer' normally would,
--   but with one important difference:
--   where 'inferBody' would normally get the actual inference results of its child nodes,
--   placeholders are generated in their place via 'inferOfNewUnbound'.
-- * Globally sort all of the tree nodes according to a given node prioritization
--   (this prioritization would be custom for each language)
-- * According to the order of prioritization,
--   attempt to unify each infer-result with its placeholder using 'inferOfUnify'.
--   If a unification fails, roll back its state changes.
--   The nodes whose unification failed are the ones assigned with type errors.
--
-- [Lamdu](https://github.com/lamdu/lamdu) uses this algorithm for its "insist type" feature,
-- which moves around the blame for type mismatches.
--
-- Note: If a similar algorithm already existed somewhere,
-- [I](https://github.com/yairchu/) would very much like to know!

{-# LANGUAGE FlexibleContexts, DefaultSignatures, TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, RankNTypes, GADTs #-}

module AST.Infer.Blame
    ( blame
    , Blame(..)
    , BTerm(..), InferOf', bAnn, bRes, bVal
    , bTermToAnn
    ) where

import AST
import AST.Class.Infer
import AST.Class.Infer.Recursive
import AST.Class.Traversable (ContainedK(..))
import AST.Class.Unify (Unify, UVarOf)
import AST.Combinator.Flip
import AST.Infer.Term (ITermVarsConstraint(..))
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.Unify.Occurs (occursCheck)
import Control.Lens (makeLenses, from)
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
-- The 'blamableRecursive' method represents that 'Blame' applies to all recursive child nodes.
-- It replaces context for 'Blame' to avoid @UndecidableSuperClasses@.
class
    (Infer m t, RTraversable t, KTraversable (InferOf t)) =>
    Blame m t where

    -- | Create a new unbound infer result.
    --
    -- The type or values within should be unbound unification variables.
    inferOfNewUnbound ::
        Proxy t ->
        m (Tree (InferOf t) (UVarOf m))

    -- | Unify the types/values in infer results
    inferOfUnify ::
        Proxy t ->
        Tree (InferOf t) (UVarOf m) ->
        Tree (InferOf t) (UVarOf m) ->
        m ()

    -- | Check whether two infer results are the same
    inferOfMatches ::
        Proxy t ->
        Tree (InferOf t) (UVarOf m) ->
        Tree (InferOf t) (UVarOf m) ->
        m Bool

    -- TODO: Putting documentation here causes duplication in the haddock documentation
    blamableRecursive ::
        Proxy m -> Proxy t -> Dict (KNodesConstraint t (Blame m))
    {-# INLINE blamableRecursive #-}
    default blamableRecursive ::
        KNodesConstraint t (Blame m) =>
        Proxy m -> Proxy t -> Dict (KNodesConstraint t (Blame m))
    blamableRecursive _ _ = Dict

instance Recursive (Blame m) where
    recurse p =
        blamableRecursive
        ((const Proxy :: p (b m t) -> Proxy m) p)
        ((const Proxy :: p (b m t) -> Proxy t) p)

-- | A type synonym to help 'BTerm' be more succinct
type InferOf' e v = Tree (InferOf (GetKnot e)) v

-- Internal Knot for the blame algorithm
data PTerm a v e = PTerm
    { pAnn :: a
    , pInferResultFromPos :: InferOf' e v
    , pInferResultFromSelf :: InferOf' e v
    , pBody :: e # PTerm a v
    }

prepareH ::
    forall m exp a.
    Blame m exp =>
    Tree (Ann a) exp ->
    m (Tree (PTerm a (UVarOf m)) exp)
prepareH t =
    inferOfNewUnbound (Proxy @exp) >>= (`prepare` t)

prepare ::
    forall m exp a.
    Blame m exp =>
    Tree (InferOf exp) (UVarOf m) ->
    Tree (Ann a) exp ->
    m (Tree (PTerm a (UVarOf m)) exp)
prepare resFromPosition (Ann a x) =
    withDict (recurse (Proxy @(Blame m exp))) $
    do
        (xI, r) <-
            mapK
            (Proxy @(Blame m) #>
                InferChild . fmap (\t -> InferredChild t (pInferResultFromPos t)) . prepareH)
            x
            & inferBody
        pure PTerm
            { pAnn = a
            , pInferResultFromPos = resFromPosition
            , pInferResultFromSelf = r
            , pBody = xI
            }

tryUnify ::
    forall err m exp.
    (MonadError err m, Blame m exp) =>
    Proxy exp ->
    Tree (InferOf exp) (UVarOf m) ->
    Tree (InferOf exp) (UVarOf m) ->
    m ()
tryUnify p i0 i1 =
    withDict (inferContext (Proxy @m) p) $
    do
        inferOfUnify p i0 i1
        traverseK_ (Proxy @(Unify m) #> occursCheck) i0
    & (`catchError` const (pure ()))

toUnifies ::
    forall err m exp a.
    (MonadError err m, Blame m exp) =>
    Tree (PTerm a (UVarOf m)) exp ->
    Tree (Ann (a, m ())) exp
toUnifies (PTerm a i0 i1 b) =
    withDict (recurse (Proxy @(Blame m exp))) $
    mapK (Proxy @(Blame m) #> toUnifies) b
    & Ann (a, tryUnify (Proxy @exp) i0 i1)

-- | A 'Knot' for an inferred term with type mismatches - the output of 'blame'
data BTerm a v e = BTerm
    { _bAnn :: a
        -- ^ The node's original annotation as passed to 'blame'
    , _bRes :: Either (InferOf' e v, InferOf' e v) (InferOf' e v)
        -- ^ Either an infer result, or two conflicting results representing a type mismatch
    , _bVal :: e # BTerm a v
        -- ^ The node's body and its inferred child nodes
    } deriving Generic
makeLenses ''BTerm
makeCommonInstances [''BTerm]

instance KNodes (Flip (BTerm a) e) where
    type KNodesConstraint (Flip (BTerm a) e) c = ITermVarsConstraint c e
    data KWitness (Flip (BTerm a) e) n where
        E_Flip_BTerm_InferOf_e ::
            KWitness (InferOf e) n ->
            KWitness (Flip (BTerm a) e) n
        E_Flip_BTerm_e ::
            KWitness e f ->
            KWitness (Flip (BTerm a) f) n ->
            KWitness (Flip (BTerm a) e) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint w p =
        withDict (iTermVarsConstraintCtx p (Proxy @e)) $
        case w of
        E_Flip_BTerm_InferOf_e w0 -> kLiftConstraint w0 p
        E_Flip_BTerm_e w0 w1 ->
            kLiftConstraint w0 (p0 p) (kLiftConstraint w1 p)
            where
                p0 :: Proxy c -> Proxy (ITermVarsConstraint c)
                p0 _ = Proxy

instance (RFunctor e, RFunctorInferOf e) => KFunctor (Flip (BTerm a) e) where
    {-# INLINE mapK #-}
    mapK f =
        withDict (recurse (Proxy @(RFunctor e))) $
        withDict (recurse (Proxy @(RFunctorInferOf e))) $
        _Flip %~
        \(BTerm pl r x) ->
        BTerm pl
        ( case r of
            Left (r0, r1) -> Left (mapRes r0, mapRes r1)
            Right r0 -> Right (mapRes r0)
        )
        ( mapK
            ( Proxy @RFunctor #*# Proxy @RFunctorInferOf #*#
                \w -> from _Flip %~ mapK (f . E_Flip_BTerm_e w)
            ) x
        )
        where
            mapRes = mapK (f . E_Flip_BTerm_InferOf_e)

instance (RFoldable e, RFoldableInferOf e) => KFoldable (Flip (BTerm a) e) where
    {-# INLINE foldMapK #-}
    foldMapK f (MkFlip (BTerm _ r x)) =
        withDict (recurse (Proxy @(RFoldable e))) $
        withDict (recurse (Proxy @(RFoldableInferOf e))) $
        case r of
        Left (r0, r1) -> foldRes r0 <> foldRes r1
        Right r0 -> foldRes r0
        <>
        foldMapK
        ( Proxy @RFoldable #*# Proxy @RFoldableInferOf #*#
            \w -> foldMapK (f . E_Flip_BTerm_e w) . (_Flip #)
        ) x
        where
            foldRes = foldMapK (f . E_Flip_BTerm_InferOf_e)

instance
    (RTraversable e, RTraversableInferOf e) =>
    KTraversable (Flip (BTerm a) e) where
    {-# INLINE sequenceK #-}
    sequenceK =
        withDict (recurse (Proxy @(RTraversable e))) $
        withDict (recurse (Proxy @(RTraversableInferOf e))) $
        _Flip
        ( \(BTerm pl r x) ->
            BTerm pl
            <$> ( case r of
                    Left (r0, r1) -> (,) <$> seqRes r0 <*> seqRes r1 <&> Left
                    Right r0 -> seqRes r0 <&> Right
                )
            <*> traverseK
                ( Proxy @RTraversable #*# Proxy @RTraversableInferOf #>
                    from _Flip sequenceK
                ) x
        )
        where
            seqRes ::
                (KTraversable k, Applicative f) =>
                Tree k (ContainedK f p) -> f (Tree k p)
            seqRes = traverseK (const runContainedK)

finalize ::
    forall a m exp.
    Blame m exp =>
    Tree (PTerm a (UVarOf m)) exp ->
    m (Tree (BTerm a (UVarOf m)) exp)
finalize (PTerm a i0 i1 x) =
    withDict (recurse (Proxy @(Blame m exp))) $
    do
        match <- inferOfMatches (Proxy @exp) i0 i1
        let result
                | match = Right i0
                | otherwise = Left (i0, i1)
        traverseK (Proxy @(Blame m) #> finalize) x
            <&> BTerm a result

-- | Perform Hindley-Milner type inference with prioritised blame for type error,
-- given a prioritisation for the different nodes.
--
-- The purpose of the prioritisation is to place the errors in nodes where
-- the resulting errors will be easier to understand.
--
-- The expected `MonadError` behavior is that catching errors rolls back their state changes
-- (i.e @StateT s (Either e)@ is suitable but @EitherT e (State s)@ is not)
--
-- Gets the top-level type for the term for support of recursive definitions,
-- where the top-level type of the term may be in the scope of the inference monad.
blame ::
    forall priority err m exp a.
    ( Ord priority
    , MonadError err m
    , Blame m exp
    ) =>
    (a -> priority) ->
    Tree (InferOf exp) (UVarOf m) ->
    Tree (Ann a) exp ->
    m (Tree (BTerm a (UVarOf m)) exp)
blame order topLevelType e =
    do
        p <- prepare topLevelType e
        toUnifies p ^.. annotations & sortOn (order . fst) & traverse_ snd
        finalize p

bTermToAnn ::
    forall a v e r.
    RFunctor e =>
    ( forall n.
        KRecWitness e n ->
        a ->
        Either (Tree (InferOf n) v, Tree (InferOf n) v) (Tree (InferOf n) v) ->
        r
    ) ->
    Tree (BTerm a v) e ->
    Tree (Ann r) e
bTermToAnn f (BTerm pl r x) =
    withDict (recurse (Proxy @(RFunctor e))) $
    mapK
    ( Proxy @RFunctor #*#
        \w -> bTermToAnn (f . KRecSub w)
    ) x
    & Ann (f KRecSelf pl r)
