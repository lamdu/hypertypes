{-# LANGUAGE TemplateHaskell, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, DefaultSignatures #-}
{-# OPTIONS -Wno-redundant-constraints #-} -- Work around false GHC warnings

module AST.Infer.Term
    ( ITerm(..), iVal, iRes, iAnn
    , iAnnotations
    , TraverseITermWith(..), traverseITermWith
    ) where

import AST
import AST.Class.Infer
import Control.Lens (Traversal, makeLenses)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
data ITerm a v e = ITerm
    { _iAnn :: a
    , _iRes :: !(Tree (InferOf (RunKnot e)) v)
    , _iVal :: Node e (ITerm a v)
    }
makeLenses ''ITerm

iAnnotations ::
    forall e a b v.
    RTraversable e =>
    Traversal
    (Tree (ITerm a v) e)
    (Tree (ITerm b v) e)
    a b
iAnnotations f (ITerm pl r x) =
    recurse (Proxy @(RTraversable e)) $
    ITerm
    <$> f pl
    <*> pure r
    <*> traverseKWith (Proxy @RTraversable) (iAnnotations f) x

class (RTraversable e, KTraversable (InferOf e)) => TraverseITermWith c e where
    traverseITermWithRecursive ::
        Proxy c -> Proxy e -> (NodesConstraint e (TraverseITermWith c) => r) -> r
    {-# INLINE traverseITermWithRecursive #-}
    default traverseITermWithRecursive ::
        NodesConstraint e (TraverseITermWith c) =>
        Proxy c -> Proxy e -> (NodesConstraint e (TraverseITermWith c) => r) -> r
    traverseITermWithRecursive _ _ = id
    traverseITermWithConstraint ::
        Proxy c -> Proxy e -> (NodesConstraint (InferOf e) c => r) -> r
    {-# INLINE traverseITermWithConstraint #-}
    default traverseITermWithConstraint ::
        NodesConstraint (InferOf e) c =>
        Proxy c -> Proxy e -> (NodesConstraint (InferOf e) c => r) -> r
    traverseITermWithConstraint _ _ = id

traverseITermWith ::
    forall e f v r a constraint.
    (TraverseITermWith constraint e, Applicative f) =>
    Proxy constraint ->
    (forall c. constraint c => Tree v c -> f (Tree r c)) ->
    Tree (ITerm a v) e -> f (Tree (ITerm a r) e)
traverseITermWith p f (ITerm a r x) =
    traverseITermWithRecursive p (Proxy @e) $
    traverseITermWithConstraint p (Proxy @e) $
    ITerm a
    <$> traverseKWith p f r
    <*> traverseKWith (Proxy @(TraverseITermWith constraint)) (traverseITermWith p f) x

deriving instance (Show a, Show (Tree e (ITerm a v)), Show (Tree (InferOf e) v)) => Show (Tree (ITerm a v) e)
