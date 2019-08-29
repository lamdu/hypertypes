{-# LANGUAGE TemplateHaskell, RecordWildCards, FlexibleContexts, DefaultSignatures #-}

module AST.Class.Infer
    ( InferOf
    , Infer(..)
    , InferRes(..), inferResVal, inferResBody
    , InferChild(..), _InferChild
    , InferredChild(..), inType, inRep
    , HasInferredValue(..)
    , HasInferredType(..)
    , LocalScopeType(..)
    ) where

import AST
import AST.Class.Unify
import Control.Lens (Lens, Lens', ALens', makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Constraint (Dict(..), withDict)
import Data.Kind (Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | @InferOf e@ is the inference result of @e@.
--
-- Most commonly it is an inferred type, using
--
-- > type instance InferOf MyTerm = ANode MyType
--
-- But it may also be other things, for example:
--
-- * An inferred value (for types inside terms)
-- * An inferred type together with a scope

type family InferOf (t :: Knot -> Type) :: Knot -> Type

-- | @HasInferredValue t@ represents that @InferOf t@ contains an inferred value for @t@.
class HasInferredValue t where
    -- | A 'Control.Lens.Lens' from an inference result to an inferred value
    inferredValue :: Lens' (Tree (InferOf t) v) (Tree v t)

class HasInferredType t where
    type TypeOf t :: Knot -> Type
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

-- | A 'Knot' storing an inference action.
--
-- The caller may modify the scope before invoking the action via
-- 'localScopeType' or 'AST.Infer.ScopeLevel.localLevel'
newtype InferChild m k t =
    InferChild { inferChild :: m (InferredChild (UVarOf m) k t) }
makePrisms ''InferChild

-- | An inferred expression body. The result of 'inferBody'
data InferRes v k t = InferRes
    { __inferResBody :: !(Tree t k)
        -- ^ The expression body with inferred child nodes
    , _inferResVal :: !(Tree (InferOf t) v)
        -- ^ The inference result for the top-level expression
    }
makeLenses ''InferRes

-- | A type-changing 'Lens' from 'InferRes' to its body field
inferResBody ::
    InferOf t0 ~ InferOf t1 =>
    Lens (InferRes v k0 t0) (InferRes v k1 t1) (Tree t0 k0) (Tree t1 k1)
inferResBody f InferRes{..} =
    f __inferResBody <&> \__inferResBody -> InferRes{..}

-- | @Infer m t@ enables 'AST.Infer.infer' to perform type-inference for @t@ in the @m@ 'Monad'.
--
-- The 'inferContext' method represents the following constraints on @t@:
--
-- * @NodesConstraint (InferOf t) (Unify m)@ - The child nodes of the inferrence can unify in the @m@ 'Monad'
-- * @NodesConstraint t (Infer m)@ - @Infer m@ is also available for child nodes
--
-- It replaces context for the 'Infer' class to avoid @UndecidableSuperClasses@.
--
-- Instances usually don't need to implement this method as the default implementation works for them,
-- but infinitely polymorphic trees such as 'AST.Term.NamelessScope.Scope' do need to implement the method,
-- because the required context is infinite.
class (Monad m, KFunctor t) => Infer m t where
    -- | Infer the body of an expression given the inference actions for its child nodes.
    inferBody ::
        Tree t (InferChild m k) ->
        m (InferRes (UVarOf m) k t)

    -- TODO: Find how to move documentation to here without haddock duplicating it for the default method
    inferContext ::
        Proxy m ->
        Proxy t ->
        Dict (NodesConstraint t (Infer m), NodesConstraint (InferOf t) (Unify m))
    {-# INLINE inferContext #-}
    default inferContext ::
        (NodesConstraint t (Infer m), NodesConstraint (InferOf t) (Unify m)) =>
        Proxy m ->
        Proxy t ->
        Dict (NodesConstraint t (Infer m), NodesConstraint (InferOf t) (Unify m))
    inferContext _ _ = Dict

instance Recursive (Infer m) where
    {-# INLINE recurse #-}
    recurse p =
        withDict (inferContext (p0 p) (p1 p)) Dict
        where
            p0 :: Proxy (Infer m t) -> Proxy m
            p0 _ = Proxy
            p1 :: Proxy (Infer m t) -> Proxy t
            p1 _ = Proxy

-- | @LocalScopeType var scheme m@ represents that @m@ maintains a scope mapping variables of type @var@ to type schemes of type @scheme@
class LocalScopeType var scheme m where
    -- | Add a variable type into an action's scope
    localScopeType :: var -> scheme -> m a -> m a
