{-# LANGUAGE TemplateHaskell, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, DefaultSignatures #-}

module AST.Infer.Term
    ( ITerm(..), iVal, iRes, iAnn
    , iAnnotations
    , traverseITermWith, TraverseITermWith(..)
    ) where

import AST
import AST.Class.Infer
import AST.TH.Internal.Instances (makeCommonInstances)
import Control.Lens (Traversal, makeLenses)
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
    <*> traverseKWith (Proxy @RTraversable) (iAnnotations f) x

-- | A class representing the requirements of 'traverseITermWith'
class (RTraversable e, KTraversable (InferOf e)) => TraverseITermWith c e where
    traverseITermWithConstraints ::
        Proxy c -> Proxy e -> Dict (NodesConstraint e (TraverseITermWith c), NodesConstraint (InferOf e) c)
    {-# INLINE traverseITermWithConstraints #-}
    default traverseITermWithConstraints ::
        (NodesConstraint e (TraverseITermWith c), NodesConstraint (InferOf e) c) =>
        Proxy c -> Proxy e -> Dict (NodesConstraint e (TraverseITermWith c), NodesConstraint (InferOf e) c)
    traverseITermWithConstraints _ _ = Dict

-- | 'traverseK' equivalent for 'ITerm', which applies on the unification variable knot
-- (not the last type parameter as 'traverseK' normally does).
--
-- /TODO/: Possibly replace with a 'KTraversable' instance for @Flip (ITerm a) e@
traverseITermWith ::
    forall e f v r a constraint.
    (TraverseITermWith constraint e, Applicative f) =>
    Proxy constraint ->
    (forall c. constraint c => Tree v c -> f (Tree r c)) ->
    Tree (ITerm a v) e -> f (Tree (ITerm a r) e)
traverseITermWith p f (ITerm a r x) =
    withDict (traverseITermWithConstraints p (Proxy @e)) $
    ITerm a
    <$> traverseKWith p f r
    <*> traverseKWith (Proxy @(TraverseITermWith constraint)) (traverseITermWith p f) x
