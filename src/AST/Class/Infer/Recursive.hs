{-# LANGUAGE DefaultSignatures, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module AST.Class.Infer.Recursive
    ( KFunctorInferOf, KFoldableInferOf, RTraversableInferOf
    ) where

import AST.Class.Nodes (KNodes(..))
import AST.Class.Foldable (KFoldable)
import AST.Class.Functor (KFunctor)
import AST.Class.Traversable (KTraversable)
import AST.Class.Infer (InferOf)
import AST.Class.Recursive (Recursive(..), Recursively)
import Data.Constraint (Dict(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

class    KFunctor (InferOf k) => KFunctorInferOf k
instance KFunctor (InferOf k) => KFunctorInferOf k
class    KFoldable (InferOf k) => KFoldableInferOf k
instance KFoldable (InferOf k) => KFoldableInferOf k

class
    (KTraversable (InferOf k), Recursively KFunctorInferOf k, Recursively KFoldableInferOf k) =>
    RTraversableInferOf k where
    rTraversableInferOfRec ::
        Proxy k -> Dict (KNodesConstraint k RTraversableInferOf)
    {-# INLINE rTraversableInferOfRec #-}
    default rTraversableInferOfRec ::
        KNodesConstraint k RTraversableInferOf =>
        Proxy k -> Dict (KNodesConstraint k RTraversableInferOf)
    rTraversableInferOfRec _ = Dict

instance Recursive RTraversableInferOf where
    {-# INLINE recurse #-}
    recurse =
        rTraversableInferOfRec . p
        where
            p :: Proxy (RTraversableInferOf k) -> Proxy k
            p _ = Proxy
