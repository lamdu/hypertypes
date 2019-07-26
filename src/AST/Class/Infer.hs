{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, RecordWildCards #-}

module AST.Class.Infer
    ( Infer(..), HasScope(..), LocalScopeType(..)
    , InferredChild(..), inType, inRep
    , InferChild(..), _InferChild
    , InferRes(..), inferResType, inferResBody
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf)
import AST.Infer.Term
import Control.Lens (Lens, makeLenses, makePrisms)
import Control.Lens.Operators

data InferredChild v k t = InferredChild
    { -- Representing the inferred child in the resulting node
      __inRep :: !(k t)
    , _inType :: !(Tree v (TypeOf (RunKnot t)))
    }
makeLenses ''InferredChild

inRep ::
    TypeOf (RunKnot t0) ~ TypeOf (RunKnot t1) =>
    Lens (InferredChild v k0 t0) (InferredChild v k1 t1) (k0 t0) (k1 t1)
inRep f InferredChild{..} =
    f __inRep <&> \__inRep -> InferredChild{..}

newtype InferChild m k t =
    InferChild { inferChild :: m (InferredChild (UVarOf m) k t) }
makePrisms ''InferChild

data InferRes v k t = InferRes
    { __inferResBody :: !(Tree t k)
    , _inferResType :: !(Tree v (TypeOf t))
    }
makeLenses ''InferRes

inferResBody ::
    TypeOf t0 ~ TypeOf t1 =>
    Lens (InferRes v k0 t0) (InferRes v k1 t1) (Tree t0 k0) (Tree t1 k1)
inferResBody f InferRes{..} =
    f __inferResBody <&> \__inferResBody -> InferRes{..}

class HasScope m s where
    getScope :: m (Tree s (UVarOf m))

class LocalScopeType var scheme m where
    localScopeType :: var -> scheme -> m a -> m a

class
    (HasScope m (ScopeOf t), Recursively (Unify m) (TypeOf t)) =>
    Infer m t where

    inferBody ::
        Tree t (InferChild m k) ->
        m (InferRes (UVarOf m) k t)
