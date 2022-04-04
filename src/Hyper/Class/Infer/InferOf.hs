{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Hyper.Class.Infer.InferOf
    ( HasInferredType(..)
    , HasInferredValue(..)
    , InferOfConstraint(..)
    ) where

import Control.Lens (ALens', Lens')
import Hyper.Class.Infer (InferOf)
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
    inferOfConstraint :: proxy h -> Dict (c (InferOf h))

instance c (InferOf h) => InferOfConstraint c h where
    inferOfConstraint _ = Dict
