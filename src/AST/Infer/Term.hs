{-# LANGUAGE TemplateHaskell, FlexibleContexts, RankNTypes, GADTs #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, DefaultSignatures #-}

module AST.Infer.Term
    ( ITerm(..), iVal, iRes, iAnn
    , ITermVarsConstraint(..)
    , iAnnotations
    , iTermToAnn
    ) where

import AST
import AST.Combinator.Flip
import AST.Class.Infer
import AST.Class.Infer.Recursive (KFunctorInferOf, KFoldableInferOf, RTraversableInferOf)
import AST.Class.Recursive (KRecWitness(..))
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
    , _iRes :: !(Tree (InferOf (GetKnot e)) v)
        -- ^ The node's inference result (such as an inferred type)
    , _iVal :: e # ITerm a v
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
        E_Flip_ITerm_InferOf_e ::
            KWitness (InferOf e) n ->
            KWitness (Flip (ITerm a) e) n
        E_Flip_ITerm_e ::
            KWitness e f ->
            KWitness (Flip (ITerm a) f) n ->
            KWitness (Flip (ITerm a) e) n
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

instance (Recursively KFunctor e, Recursively KFunctorInferOf e) => KFunctor (Flip (ITerm a) e) where
    {-# INLINE mapK #-}
    mapK f =
        withDict (recursively (Proxy @(KFunctor e))) $
        withDict (recursively (Proxy @(KFunctorInferOf e))) $
        _Flip %~
        \(ITerm pl r x) ->
        ITerm pl
        (mapK (f . E_Flip_ITerm_InferOf_e) r)
        ( mapK
            ( Proxy @(Recursively KFunctor) #*# Proxy @(Recursively KFunctorInferOf) #*#
                \w -> from _Flip %~ mapK (f . E_Flip_ITerm_e w)
            ) x
        )

instance (Recursively KFoldable e, Recursively KFoldableInferOf e) => KFoldable (Flip (ITerm a) e) where
    {-# INLINE foldMapK #-}
    foldMapK f (MkFlip (ITerm _ r x)) =
        withDict (recursively (Proxy @(KFoldable e))) $
        withDict (recursively (Proxy @(KFoldableInferOf e))) $
        foldMapK (f . E_Flip_ITerm_InferOf_e) r <>
        foldMapK
        ( Proxy @(Recursively KFoldable) #*# Proxy @(Recursively KFoldableInferOf) #*#
            \w -> foldMapK (f . E_Flip_ITerm_e w) . (_Flip #)
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

iTermToAnn ::
    forall a v e r.
    Recursively KFunctor e =>
    ( forall n.
        KRecWitness e n ->
        a ->
        Tree (InferOf n) v ->
        r
    ) ->
    Tree (ITerm a v) e ->
    Tree (Ann r) e
iTermToAnn f (ITerm pl r x) =
    withDict (recursively (Proxy @(KFunctor e))) $
    mapK
    ( Proxy @(Recursively KFunctor) #*#
        \w -> iTermToAnn (f . KRecSub w)
    ) x
    & Ann (f KRecSelf pl r)
