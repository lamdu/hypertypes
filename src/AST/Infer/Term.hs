{-# LANGUAGE TemplateHaskell, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances, DefaultSignatures #-}

module AST.Infer.Term
    ( ITerm(..), iVal, iRes, iAnn
    , iAnnotations, iTermToAnn
    , TraverseITermWith(..), traverseITermWith
    ) where

import AST
import AST.Class.Infer
import AST.Class.Recursive
import AST.TH.Internal.Instances (makeCommonInstances)
import Control.Lens (Traversal, makeLenses)
import Data.Constraint
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
data ITerm a v e = ITerm
    { _iAnn :: a
    , _iRes :: !(Tree (InferOf (RunKnot e)) v)
    , _iVal :: Node e (ITerm a v)
    } deriving Generic
makeLenses ''ITerm
makeCommonInstances [''ITerm]

iAnnotations ::
    forall e a b v.
    RTraversable e =>
    Traversal
    (Tree (ITerm a v) e)
    (Tree (ITerm b v) e)
    a b
iAnnotations f (ITerm pl r x) =
    withDict (recursiveKTraversable (Proxy @e)) $
    ITerm
    <$> f pl
    <*> pure r
    <*> traverseKWith (Proxy @RTraversable) (iAnnotations f) x

iTermToAnn ::
    forall f e a v r c.
    (Applicative f, RTraversable e, c e, Recursive c) =>
    Proxy c ->
    (forall n. c n => Proxy n -> Tree (InferOf n) v -> f r) ->
    Tree (ITerm a v) e ->
    f (Tree (Ann (a, r)) e)
iTermToAnn p f (ITerm a i x) =
    withDict (recurseBoth (Proxy @(And RTraversable c e))) $
    (\r b -> Ann (a, r) b)
    <$> f (Proxy @e) i
    <*> traverseKWith (Proxy @(And RTraversable c)) (iTermToAnn p f) x

class (RTraversable e, KTraversable (InferOf e)) => TraverseITermWith c e where
    traverseITermWithRecursive :: Proxy c -> Proxy e -> Dict (NodesConstraint e (TraverseITermWith c))
    {-# INLINE traverseITermWithRecursive #-}
    default traverseITermWithRecursive ::
        NodesConstraint e (TraverseITermWith c) =>
        Proxy c -> Proxy e -> Dict (NodesConstraint e (TraverseITermWith c))
    traverseITermWithRecursive _ _ = Dict
    traverseITermWithConstraint :: Proxy c -> Proxy e -> Dict (NodesConstraint (InferOf e) c)
    {-# INLINE traverseITermWithConstraint #-}
    default traverseITermWithConstraint ::
        NodesConstraint (InferOf e) c =>
        Proxy c -> Proxy e -> Dict (NodesConstraint (InferOf e) c)
    traverseITermWithConstraint _ _ = Dict

traverseITermWith ::
    forall e f v r a constraint.
    (TraverseITermWith constraint e, Applicative f) =>
    Proxy constraint ->
    (forall c. constraint c => Tree v c -> f (Tree r c)) ->
    Tree (ITerm a v) e -> f (Tree (ITerm a r) e)
traverseITermWith p f (ITerm a r x) =
    withDict (traverseITermWithRecursive p (Proxy @e)) $
    withDict (traverseITermWithConstraint p (Proxy @e)) $
    ITerm a
    <$> traverseKWith p f r
    <*> traverseKWith (Proxy @(TraverseITermWith constraint)) (traverseITermWith p f) x
