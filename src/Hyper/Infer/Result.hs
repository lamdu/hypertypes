{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, DefaultSignatures #-}

module Hyper.Infer.Result
    ( ITerm(..), iVal, iRes, iAnn
    , ITermVarsConstraint(..)
    , iAnnotations
    , iTermToAnn
    ) where

import Hyper
import Hyper.Type.Combinator.Flip
import Hyper.Class.Infer
import Hyper.Class.Infer.InferOf (HFunctorInferOf, HFoldableInferOf, RTraversableInferOf)
import Hyper.Class.Traversable (ContainedK(..))
import Hyper.Recurse
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Control.Lens (Traversal, makeLenses, from)
import Control.Lens.Operators
import Data.Constraint
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

-- | A 'AHyperType' for an inferred term - the output of 'Hyper.Infer.infer'
data ITerm a v e = ITerm
    { _iAnn :: a
        -- ^ The node's original annotation as passed to 'Hyper.Infer.infer'
    , _iRes :: !(Tree (InferOf (GetHyperType e)) v)
        -- ^ The node's inference result (such as an inferred type)
    , _iVal :: e # ITerm a v
        -- ^ The node's body and its inferred child nodes
    } deriving Generic
makeLenses ''ITerm
makeCommonInstances [''ITerm]

type ITermVarsConstraintContext c e =
    ( HNodes (InferOf e)
    , HNodesConstraint (InferOf e) c
    , HNodes e
    , HNodesConstraint e (ITermVarsConstraint c)
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

instance HNodes (Flip (ITerm a) e) where
    type HNodesConstraint (Flip (ITerm a) e) c = ITermVarsConstraint c e
    data HWitness (Flip (ITerm a) e) n where
        E_Flip_ITerm_InferOf_e ::
            HWitness (InferOf e) n ->
            HWitness (Flip (ITerm a) e) n
        E_Flip_ITerm_e ::
            HWitness e f ->
            HWitness (Flip (ITerm a) f) n ->
            HWitness (Flip (ITerm a) e) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint w p =
        withDict (iTermVarsConstraintCtx p (Proxy @e)) $
        case w of
        E_Flip_ITerm_InferOf_e w0 -> kLiftConstraint w0 p
        E_Flip_ITerm_e w0 w1 ->
            kLiftConstraint w0 (p0 p) (kLiftConstraint w1 p)
            where
                p0 :: Proxy c -> Proxy (ITermVarsConstraint c)
                p0 _ = Proxy

instance (Recursively HFunctor e, Recursively HFunctorInferOf e) => HFunctor (Flip (ITerm a) e) where
    {-# INLINE mapK #-}
    mapK f =
        withDict (recursively (Proxy @(HFunctor e))) $
        withDict (recursively (Proxy @(HFunctorInferOf e))) $
        _Flip %~
        \(ITerm pl r x) ->
        ITerm pl
        (mapK (f . E_Flip_ITerm_InferOf_e) r)
        ( mapK
            ( Proxy @(Recursively HFunctor) #*# Proxy @(Recursively HFunctorInferOf) #*#
                \w -> from _Flip %~ mapK (f . E_Flip_ITerm_e w)
            ) x
        )

instance (Recursively HFoldable e, Recursively HFoldableInferOf e) => HFoldable (Flip (ITerm a) e) where
    {-# INLINE foldMapK #-}
    foldMapK f (MkFlip (ITerm _ r x)) =
        withDict (recursively (Proxy @(HFoldable e))) $
        withDict (recursively (Proxy @(HFoldableInferOf e))) $
        foldMapK (f . E_Flip_ITerm_InferOf_e) r <>
        foldMapK
        ( Proxy @(Recursively HFoldable) #*# Proxy @(Recursively HFoldableInferOf) #*#
            \w -> foldMapK (f . E_Flip_ITerm_e w) . (_Flip #)
        ) x

instance
    (RTraversable e, RTraversableInferOf e) =>
    HTraversable (Flip (ITerm a) e) where
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

iTermToAnn ::
    forall a v e r.
    Recursively HFunctor e =>
    ( forall n.
        HRecWitness e n ->
        a ->
        Tree (InferOf n) v ->
        r
    ) ->
    Tree (ITerm a v) e ->
    Tree (Ann r) e
iTermToAnn f (ITerm pl r x) =
    withDict (recursively (Proxy @(HFunctor e))) $
    mapK
    ( Proxy @(Recursively HFunctor) #*#
        \w -> iTermToAnn (f . HRecSub w)
    ) x
    & Ann (f HRecSelf pl r)
