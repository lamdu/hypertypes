{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}

module AST.Class.Infer.Recursive
    ( RFunctorInferOf, RFoldableInferOf, RTraversableInferOf
    ) where

import AST.Class.Nodes (KNodes(..))
import AST.Class.Foldable (KFoldable)
import AST.Class.Functor (KFunctor)
import AST.Class.Traversable (KTraversable)
import AST.Class.Infer (InferOf)
import AST.Class.Recursive (Recursive(..))
import AST.Knot (Knot)
import Data.Constraint (Dict(..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class KFunctor (InferOf k) => RFunctorInferOf k where
    rFunctorInferOfRec ::
        Proxy k -> Dict (KNodesConstraint k RFunctorInferOf)
    {-# INLINE rFunctorInferOfRec #-}
    default rFunctorInferOfRec ::
        KNodesConstraint k RFunctorInferOf =>
        Proxy k -> Dict (KNodesConstraint k RFunctorInferOf)
    rFunctorInferOfRec _ = Dict

instance Recursive RFunctorInferOf where
    {-# INLINE recurse #-}
    recurse = rFunctorInferOfRec . argP

argP :: Proxy (f k :: Constraint) -> Proxy (k :: Knot -> Type)
argP _ = Proxy

class KFoldable (InferOf k) => RFoldableInferOf k where
    rFoldableInferOfRec ::
        Proxy k -> Dict (KNodesConstraint k RFoldableInferOf)
    {-# INLINE rFoldableInferOfRec #-}
    default rFoldableInferOfRec ::
        KNodesConstraint k RFoldableInferOf =>
        Proxy k -> Dict (KNodesConstraint k RFoldableInferOf)
    rFoldableInferOfRec _ = Dict

instance Recursive RFoldableInferOf where
    {-# INLINE recurse #-}
    recurse = rFoldableInferOfRec . argP

class
    (KTraversable (InferOf k), RFunctorInferOf k, RFoldableInferOf k) =>
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
    recurse = rTraversableInferOfRec . argP
