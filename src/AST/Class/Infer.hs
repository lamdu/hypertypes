{-# LANGUAGE TemplateHaskell, RecordWildCards, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableSuperClasses, UndecidableInstances #-}

module AST.Class.Infer
    ( Infer(..), HasScope(..), LocalScopeType(..)
    , InferredChild(..), inType, inRep
    , InferChild(..), _InferChild
    , InferRes(..), inferResVal, inferResBody
    , InferOf, InferOfConstraint
    ) where

import AST
import AST.Class.Unify (UVarOf)
import Control.Lens (Lens, makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Kind (Type)

import Prelude.Compat

type family InferOf (t :: Knot -> Type) :: Knot -> Type

class    c (InferOf t) => InferOfConstraint c t
instance c (InferOf t) => InferOfConstraint c t

data InferredChild v k t = InferredChild
    { -- Representing the inferred child in the resulting node
      __inRep :: !(k t)
    , _inType :: !(Tree (InferOf (RunKnot t)) v)
    }
makeLenses ''InferredChild

inRep ::
    InferOf (RunKnot t0) ~ InferOf (RunKnot t1) =>
    Lens (InferredChild v k0 t0) (InferredChild v k1 t1) (k0 t0) (k1 t1)
inRep f InferredChild{..} =
    f __inRep <&> \__inRep -> InferredChild{..}

newtype InferChild m k t =
    InferChild { inferChild :: m (InferredChild (UVarOf m) k t) }
makePrisms ''InferChild

data InferRes v k t = InferRes
    { __inferResBody :: !(Tree t k)
    , _inferResVal :: !(Tree (InferOf t) v)
    }
makeLenses ''InferRes

inferResBody ::
    InferOf t0 ~ InferOf t1 =>
    Lens (InferRes v k0 t0) (InferRes v k1 t1) (Tree t0 k0) (Tree t1 k1)
inferResBody f InferRes{..} =
    f __inferResBody <&> \__inferResBody -> InferRes{..}

class HasScope m s where
    getScope :: m (Tree s (UVarOf m))

class LocalScopeType var scheme m where
    localScopeType :: var -> scheme -> m a -> m a

class Monad m => Infer m t where
    inferBody ::
        Tree t (InferChild m k) ->
        m (InferRes (UVarOf m) k t)
