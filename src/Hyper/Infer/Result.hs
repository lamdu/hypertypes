{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, DefaultSignatures #-}

module Hyper.Infer.Result
    ( Inferred(..), iVal, iRes, iAnn
    , InferredVarsConstraint(..)
    , iAnnotations
    , inferredToAnn
    ) where

import Control.Lens (Traversal, makeLenses, from)
import Control.Lens.Operators
import Data.Constraint
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)
import Hyper
import Hyper.Class.Infer
import Hyper.Class.Infer.InferOf (HFunctorInferOf, HFoldableInferOf, RTraversableInferOf)
import Hyper.Class.Traversable (ContainedK(..))
import Hyper.Recurse
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.Type.Combinator.Flip

import Prelude.Compat

-- | A 'AHyperType' for an inferred term - the output of 'Hyper.Infer.infer'
data Inferred a v e = Inferred
    { _iAnn :: a
        -- ^ The node's original annotation as passed to 'Hyper.Infer.infer'
    , _iRes :: !(Tree (InferOf (GetHyperType e)) v)
        -- ^ The node's inference result (such as an inferred type)
    , _iVal :: e # Inferred a v
        -- ^ The node's body and its inferred child nodes
    } deriving Generic
makeLenses ''Inferred
makeCommonInstances [''Inferred]

type InferredVarsConstraintContext c e =
    ( HNodes (InferOf e)
    , HNodesConstraint (InferOf e) c
    , HNodes e
    , HNodesConstraint e (InferredVarsConstraint c)
    )

class InferredVarsConstraint c e where
    inferredVarsConstraintCtx ::
        Proxy c -> Proxy e ->
        Dict (InferredVarsConstraintContext c e)
    default inferredVarsConstraintCtx ::
        InferredVarsConstraintContext c e =>
        Proxy c -> Proxy e ->
        Dict (InferredVarsConstraintContext c e)
    inferredVarsConstraintCtx _ _ = Dict

instance Recursive (InferredVarsConstraint c) where
    recurse p =
        withDict (r p) Dict
        where
            r ::
                forall h.
                InferredVarsConstraint c h =>
                Proxy (InferredVarsConstraint c h) ->
                Dict (InferredVarsConstraintContext c h)
            r _ = inferredVarsConstraintCtx (Proxy @c) (Proxy @h)

instance HNodes (Flip (Inferred a) e) where
    type HNodesConstraint (Flip (Inferred a) e) c = InferredVarsConstraint c e
    data HWitness (Flip (Inferred a) e) n where
        E_Flip_Inferred_InferOf_e ::
            HWitness (InferOf e) n ->
            HWitness (Flip (Inferred a) e) n
        E_Flip_Inferred_e ::
            HWitness e f ->
            HWitness (Flip (Inferred a) f) n ->
            HWitness (Flip (Inferred a) e) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint w p =
        withDict (inferredVarsConstraintCtx p (Proxy @e)) $
        case w of
        E_Flip_Inferred_InferOf_e w0 -> kLiftConstraint w0 p
        E_Flip_Inferred_e w0 w1 ->
            kLiftConstraint w0 (p0 p) (kLiftConstraint w1 p)
            where
                p0 :: Proxy c -> Proxy (InferredVarsConstraint c)
                p0 _ = Proxy

instance (Recursively HFunctor e, Recursively HFunctorInferOf e) => HFunctor (Flip (Inferred a) e) where
    {-# INLINE mapK #-}
    mapK f =
        withDict (recursively (Proxy @(HFunctor e))) $
        withDict (recursively (Proxy @(HFunctorInferOf e))) $
        _Flip %~
        \(Inferred pl r x) ->
        Inferred pl
        (mapK (f . E_Flip_Inferred_InferOf_e) r)
        ( mapK
            ( Proxy @(Recursively HFunctor) #*# Proxy @(Recursively HFunctorInferOf) #*#
                \w -> from _Flip %~ mapK (f . E_Flip_Inferred_e w)
            ) x
        )

instance (Recursively HFoldable e, Recursively HFoldableInferOf e) => HFoldable (Flip (Inferred a) e) where
    {-# INLINE foldMapK #-}
    foldMapK f (MkFlip (Inferred _ r x)) =
        withDict (recursively (Proxy @(HFoldable e))) $
        withDict (recursively (Proxy @(HFoldableInferOf e))) $
        foldMapK (f . E_Flip_Inferred_InferOf_e) r <>
        foldMapK
        ( Proxy @(Recursively HFoldable) #*# Proxy @(Recursively HFoldableInferOf) #*#
            \w -> foldMapK (f . E_Flip_Inferred_e w) . (_Flip #)
        ) x

instance
    (RTraversable e, RTraversableInferOf e) =>
    HTraversable (Flip (Inferred a) e) where
    {-# INLINE sequenceK #-}
    sequenceK =
        withDict (recurse (Proxy @(RTraversable e))) $
        withDict (recurse (Proxy @(RTraversableInferOf e))) $
        _Flip
        ( \(Inferred pl r x) ->
            Inferred pl
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
    (Tree (Inferred a v) e)
    (Tree (Inferred b v) e)
    a b
iAnnotations f (Inferred pl r x) =
    withDict (recurse (Proxy @(RTraversable e))) $
    Inferred
    <$> f pl
    <*> pure r
    <*> traverseK (Proxy @RTraversable #> iAnnotations f) x

inferredToAnn ::
    forall a v e r.
    Recursively HFunctor e =>
    ( forall n.
        HRecWitness e n ->
        a ->
        Tree (InferOf n) v ->
        r
    ) ->
    Tree (Inferred a v) e ->
    Tree (Ann r) e
inferredToAnn f (Inferred pl r x) =
    withDict (recursively (Proxy @(HFunctor e))) $
    mapK
    ( Proxy @(Recursively HFunctor) #*#
        \w -> inferredToAnn (f . HRecSub w)
    ) x
    & Ann (f HRecSelf pl r)
