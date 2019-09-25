{-# LANGUAGE DefaultSignatures, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Hyper.Class.Infer.InferOf
    ( HasInferredType(..)
    , HasInferredValue(..)
    , HFunctorInferOf, HFoldableInferOf, RTraversableInferOf
    ) where

import Hyper.Class.Nodes (HNodes(..))
import Hyper.Class.Foldable (HFoldable)
import Hyper.Class.Functor (HFunctor)
import Hyper.Class.Traversable (HTraversable)
import Hyper.Class.Infer (InferOf)
import Hyper.Class.Recursive (Recursive(..), Recursively)
import Hyper.Type (HyperType, Tree)
import Control.Lens (ALens', Lens')
import Data.Constraint (Dict(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | @HasInferredType t@ represents that @InferOf t@ contains a @TypeOf t@, which represents its inferred type.
class HasInferredType t where
    -- | The type of @t@
    type TypeOf t :: HyperType
    -- A 'Control.Lens.Lens' from an inference result to an inferred type
    inferredType :: Proxy t -> ALens' (Tree (InferOf t) v) (Tree v (TypeOf t))

-- | @HasInferredValue t@ represents that @InferOf t@ contains an inferred value for @t@.
class HasInferredValue t where
    -- | A 'Control.Lens.Lens' from an inference result to an inferred value
    inferredValue :: Lens' (Tree (InferOf t) v) (Tree v t)

class    HFunctor (InferOf k) => HFunctorInferOf k
instance HFunctor (InferOf k) => HFunctorInferOf k
class    HFoldable (InferOf k) => HFoldableInferOf k
instance HFoldable (InferOf k) => HFoldableInferOf k

class
    (HTraversable (InferOf k), Recursively HFunctorInferOf k, Recursively HFoldableInferOf k) =>
    RTraversableInferOf k where
    rTraversableInferOfRec ::
        Proxy k -> Dict (HNodesConstraint k RTraversableInferOf)
    {-# INLINE rTraversableInferOfRec #-}
    default rTraversableInferOfRec ::
        HNodesConstraint k RTraversableInferOf =>
        Proxy k -> Dict (HNodesConstraint k RTraversableInferOf)
    rTraversableInferOfRec _ = Dict

instance Recursive RTraversableInferOf where
    {-# INLINE recurse #-}
    recurse =
        rTraversableInferOfRec . p
        where
            p :: Proxy (RTraversableInferOf k) -> Proxy k
            p _ = Proxy
