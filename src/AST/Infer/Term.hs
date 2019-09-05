{-# LANGUAGE TemplateHaskell, FlexibleContexts, RankNTypes, GADTs #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, DefaultSignatures #-}

module AST.Infer.Term
    ( ITerm(..), iVal, iRes, iAnn
    , ITermVarsConstraint(..)
    , iAnnotations
    ) where

import AST
import AST.Combinator.Flip
import AST.Class.Infer
import AST.Class.Infer.Recursive (RFunctorInferOf, RFoldableInferOf, RTraversableInferOf)
import AST.Class.Traversable (ContainedK(..))
import AST.TH.Internal.Instances (makeCommonInstances)
import Control.Lens (Traversal, makeLenses, from)
import Control.Lens.Operators
import Data.Constraint
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

-- | A 'Knot' for an inferred term - the output of 'AST.Infer.infer'
data ITerm a v e = ITerm
    { _iAnn :: a
        -- ^ The node's original annotation as passed to 'AST.Infer.infer'
    , _iRes :: !(Tree (InferOf (RunKnot e)) v)
        -- ^ The node's inference result (such as an inferred type)
    , _iVal :: Node e (ITerm a v)
        -- ^ The node's body and its inferred child nodes
    } deriving Generic
makeLenses ''ITerm
makeCommonInstances [''ITerm]

type ITermVarsConstraintContext c e =
    ( KNodes (InferOf e)
    , KNodesConstraint (InferOf e) c
    , KNodes e
    , KNodesConstraint e (ITermVarsConstraint c)
    )

class ITermVarsConstraint c e where
    iTermVarsConstraintCtx ::
        Proxy c -> Proxy e ->
        Dict (ITermVarsConstraintContext c e)
    default iTermVarsConstraintCtx ::
        ITermVarsConstraintContext c e =>
        Proxy c -> Proxy e ->
        Dict (ITermVarsConstraintContext c e)
    iTermVarsConstraintCtx _ _ = Dict

instance Recursive (ITermVarsConstraint c) where
    recurse p =
        withDict (r p) Dict
        where
            r ::
                forall k.
                ITermVarsConstraint c k =>
                Proxy (ITermVarsConstraint c k) ->
                Dict (ITermVarsConstraintContext c k)
            r _ = iTermVarsConstraintCtx (Proxy @c) (Proxy @k)

instance KNodes (Flip (ITerm a) e) where
    type KNodesConstraint (Flip (ITerm a) e) c = ITermVarsConstraint c e
    data KWitness (Flip (ITerm a) e) n where
        KW_Flip_ITerm_E0 ::
            KWitness (InferOf e) n ->
            KWitness (Flip (ITerm a) e) n
        KW_Flip_ITerm_E1 ::
            KWitness e f ->
            KWitness (Flip (ITerm a) f) n ->
            KWitness (Flip (ITerm a) e) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint w p =
        withDict (iTermVarsConstraintCtx p (Proxy @e)) $
        case w of
        KW_Flip_ITerm_E0 w0 -> kLiftConstraint w0 p
        KW_Flip_ITerm_E1 w0 w1 ->
            kLiftConstraint w0 (p0 p) (kLiftConstraint w1 p)
            where
                p0 :: Proxy c -> Proxy (ITermVarsConstraint c)
                p0 _ = Proxy

instance (RFunctor e, RFunctorInferOf e) => KFunctor (Flip (ITerm a) e) where
    {-# INLINE mapK #-}
    mapK f =
        withDict (recurse (Proxy @(RFunctor e))) $
        withDict (recurse (Proxy @(RFunctorInferOf e))) $
        _Flip %~
        \(ITerm pl r x) ->
        ITerm pl
        (mapK (f . KW_Flip_ITerm_E0) r)
        ( mapK
            ( Proxy @RFunctor #*# Proxy @RFunctorInferOf #*#
                \w -> from _Flip %~ mapK (f . KW_Flip_ITerm_E1 w)
            ) x
        )

instance (RFoldable e, RFoldableInferOf e) => KFoldable (Flip (ITerm a) e) where
    {-# INLINE foldMapK #-}
    foldMapK f (MkFlip (ITerm _ r x)) =
        withDict (recurse (Proxy @(RFoldable e))) $
        withDict (recurse (Proxy @(RFoldableInferOf e))) $
        foldMapK (f . KW_Flip_ITerm_E0) r <>
        foldMapK
        ( Proxy @RFoldable #*# Proxy @RFoldableInferOf #*#
            \w -> foldMapK (f . KW_Flip_ITerm_E1 w) . (_Flip #)
        ) x

instance
    (RTraversable e, RTraversableInferOf e) =>
    KTraversable (Flip (ITerm a) e) where
    {-# INLINE sequenceK #-}
    sequenceK =
        withDict (recurse (Proxy @(RTraversable e))) $
        withDict (recurse (Proxy @(RTraversableInferOf e))) $
        _Flip
        ( \(ITerm pl r x) ->
            ITerm pl
            <$> traverseK (const runContainedK) r
            <*> traverseK
                ( Proxy @RTraversable #*# Proxy @RTraversableInferOf #>
                    from _Flip sequenceK
                ) x
        )

-- | A 'Traversal' from an inferred term to the node annotations (not the inference results)
iAnnotations ::
    forall e a b v.
    RTraversable e =>
    Traversal
    (Tree (ITerm a v) e)
    (Tree (ITerm b v) e)
    a b
iAnnotations f (ITerm pl r x) =
    withDict (recurse (Proxy @(RTraversable e))) $
    ITerm
    <$> f pl
    <*> pure r
    <*> traverseK (Proxy @RTraversable #> iAnnotations f) x
