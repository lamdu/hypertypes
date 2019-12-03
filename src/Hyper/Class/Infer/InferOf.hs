{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Hyper.Class.Infer.InferOf
    ( HasInferredType(..)
    , HasInferredValue(..)
    , HFunctorInferOf, HFoldableInferOf, RTraversableInferOf
    ) where

import Control.Lens (ALens', Lens')
import Data.Constraint (Dict(..))
import Data.Proxy (Proxy(..))
import Hyper.Class.Foldable (HFoldable)
import Hyper.Class.Functor (HFunctor)
import Hyper.Class.Infer (InferOf)
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Class.Recursive (Recursive(..), Recursively, proxyArgument)
import Hyper.Class.Traversable (HTraversable)
import Hyper.Type (HyperType, type (#))

import Prelude.Compat

-- | @HasInferredType t@ represents that @InferOf t@ contains a @TypeOf t@, which represents its inferred type.
class HasInferredType t where
    -- | The type of @t@
    type TypeOf t :: HyperType
    -- A 'Control.Lens.Lens' from an inference result to an inferred type
    inferredType :: Proxy t -> ALens' (InferOf t # v) (v # TypeOf t)

-- | @HasInferredValue t@ represents that @InferOf t@ contains an inferred value for @t@.
class HasInferredValue t where
    -- | A 'Control.Lens.Lens' from an inference result to an inferred value
    inferredValue :: Lens' (InferOf t # v) (v # t)

class    HFunctor (InferOf h) => HFunctorInferOf h
instance HFunctor (InferOf h) => HFunctorInferOf h
class    HFoldable (InferOf h) => HFoldableInferOf h
instance HFoldable (InferOf h) => HFoldableInferOf h

class
    (HTraversable (InferOf h), Recursively HFunctorInferOf h, Recursively HFoldableInferOf h) =>
    RTraversableInferOf h where
    rTraversableInferOfRec ::
        Proxy h -> Dict (HNodesConstraint h RTraversableInferOf)
    {-# INLINE rTraversableInferOfRec #-}
    default rTraversableInferOfRec ::
        HNodesConstraint h RTraversableInferOf =>
        Proxy h -> Dict (HNodesConstraint h RTraversableInferOf)
    rTraversableInferOfRec _ = Dict

instance Recursive RTraversableInferOf where
    {-# INLINE recurse #-}
    recurse = rTraversableInferOfRec . proxyArgument
