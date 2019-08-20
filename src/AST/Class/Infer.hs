{-# LANGUAGE TemplateHaskell, RecordWildCards, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableSuperClasses, UndecidableInstances, DefaultSignatures #-}

module AST.Class.Infer
    ( Infer(..), LocalScopeType(..)
    , InferredChild(..), inType, inRep
    , InferChild(..), _InferChild
    , InferRes(..), inferResVal, inferResBody
    , Inferrable(..)
    , HasInferredValue(..)
    , HasInferredType(..), TypeOf
    ) where

import AST
import AST.Class.Unify
import Control.Lens (Lens, Lens', ALens', makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Constraint (Dict(..))
import Data.Kind (Type)
import Data.Proxy (Proxy)

import Prelude.Compat

class KTraversable t => Inferrable t where
    type family InferOf (t :: Knot -> Type) :: Knot -> Type

    inferrableRecursive :: Proxy t -> Dict (NodesConstraint t Inferrable)
    {-# INLINE inferrableRecursive #-}
    default inferrableRecursive ::
        NodesConstraint t Inferrable =>
        Proxy t -> Dict (NodesConstraint t Inferrable)
    inferrableRecursive _ = Dict

    traversableInferOf :: Proxy t -> Dict (KTraversable (InferOf t))
    {-# INLINE traversableInferOf #-}
    default traversableInferOf ::
        KTraversable (InferOf t) =>
        Proxy t -> Dict (KTraversable (InferOf t))
    traversableInferOf _ = Dict

class HasInferredValue t where
    inferredValue :: Lens' (Tree (InferOf t) v) (Tree v t)

type family TypeOf (t :: Knot -> Type) :: Knot -> Type

class HasInferredType t where
    inferredType :: Proxy t -> ALens' (Tree (InferOf t) v) (Tree v (TypeOf t))

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

class LocalScopeType var scheme m where
    localScopeType :: var -> scheme -> m a -> m a

class (Monad m, Inferrable t) => Infer m t where
    inferBody ::
        Tree t (InferChild m k) ->
        m (InferRes (UVarOf m) k t)

    inferRecursive :: Proxy m -> Proxy t -> Dict (NodesConstraint t (Infer m))
    {-# INLINE inferRecursive #-}
    default inferRecursive ::
        NodesConstraint t (Infer m) =>
        Proxy m -> Proxy t -> Dict (NodesConstraint t (Infer m))
    inferRecursive _ _ = Dict

    inferredUnify :: Proxy m -> Proxy t -> Dict (NodesConstraint (InferOf t) (Unify m))
    {-# INLINE inferredUnify #-}
    default inferredUnify ::
        NodesConstraint (InferOf t) (Unify m) =>
        Proxy m -> Proxy t -> Dict (NodesConstraint (InferOf t) (Unify m))
    inferredUnify _ _ = Dict
