{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Hyper.Class.Infer.InferOf
    ( HasInferredType(..)
    , HasInferredValue(..)
    , InferOfConstraint(..), RTraversableInferOf
    ) where

import Control.Lens (ALens', Lens')
import Hyper.Class.Foldable (HFoldable)
import Hyper.Class.Functor (HFunctor)
import Hyper.Class.Infer (InferOf)
import Hyper.Class.Recursive
import Hyper.Class.Traversable (HTraversable)
import Hyper.Type (HyperType, type (#))

import Hyper.Internal.Prelude

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

class InferOfConstraint c h where
    inferOfConstraint :: proxy0 c -> proxy1 h -> Dict (c (InferOf h))

instance c (InferOf h) => InferOfConstraint c h where
    inferOfConstraint _ _ = Dict

class
    (HTraversable (InferOf h), Recursively (InferOfConstraint HFunctor) h, Recursively (InferOfConstraint HFoldable) h) =>
    RTraversableInferOf h where
    rTraversableInferOfRec :: RecMethod RTraversableInferOf h
    {-# INLINE rTraversableInferOfRec #-}
    default rTraversableInferOfRec :: DefRecMethod RTraversableInferOf h
    rTraversableInferOfRec _ = Dict

instance Recursive RTraversableInferOf where
    {-# INLINE recurse #-}
    recurse = rTraversableInferOfRec . proxyArgument
