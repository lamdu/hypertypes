{-# LANGUAGE DefaultSignatures, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Hyper.Class.Infer.InferOf
    ( HasInferredType(..)
    , HasInferredValue(..)
    , KFunctorInferOf, KFoldableInferOf, RTraversableInferOf
    ) where

import Hyper.Class.Nodes (KNodes(..))
import Hyper.Class.Foldable (KFoldable)
import Hyper.Class.Functor (KFunctor)
import Hyper.Class.Traversable (KTraversable)
import Hyper.Class.Infer (InferOf)
import Hyper.Class.Recursive (Recursive(..), Recursively)
import Hyper.Knot (Knot, Tree)
import Control.Lens (ALens', Lens')
import Data.Constraint (Dict(..))
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | @HasInferredType t@ represents that @InferOf t@ contains a @TypeOf t@, which represents its inferred type.
class HasInferredType t where
    -- | The type of @t@
    type TypeOf t :: Knot -> Type
    -- A 'Control.Lens.Lens' from an inference result to an inferred type
    inferredType :: Proxy t -> ALens' (Tree (InferOf t) v) (Tree v (TypeOf t))

-- | @HasInferredValue t@ represents that @InferOf t@ contains an inferred value for @t@.
class HasInferredValue t where
    -- | A 'Control.Lens.Lens' from an inference result to an inferred value
    inferredValue :: Lens' (Tree (InferOf t) v) (Tree v t)

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
