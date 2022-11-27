{-# LANGUAGE TemplateHaskell, FlexibleInstances, FlexibleContexts #-}

module Hyper.Class.Infer
    ( InferOf
    , Infer(..)
    , InferChild(..), _InferChild
    , InferredChild(..), inType, inRep
    ) where

import qualified Control.Lens as Lens
import           GHC.Generics
import           Hyper
import           Hyper.Class.Unify
import           Hyper.Recurse

import           Hyper.Internal.Prelude

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
type family InferOf (t :: HyperType) :: HyperType

-- | A 'HyperType' containing an inferred child node
data InferredChild v h t = InferredChild
    { _inRep :: !(h t)
        -- ^ Inferred node.
        --
        -- An 'inferBody' implementation needs to place this value in the corresponding child node of the inferred term body
    , _inType :: !(InferOf (GetHyperType t) # v)
        -- ^ The inference result for the child node.
        --
        -- An 'inferBody' implementation may use it to perform unifications with it.
    }
makeLenses ''InferredChild

-- | A 'HyperType' containing an inference action.
--
-- The caller may modify the scope before invoking the action via
-- 'Hyper.Class.Infer.Env.localScopeType' or 'Hyper.Infer.ScopeLevel.localLevel'
newtype InferChild m h t =
    InferChild { inferChild :: m (InferredChild (UVarOf m) h t) }
makePrisms ''InferChild

-- | @Infer m t@ enables 'Hyper.Infer.infer' to perform type-inference for @t@ in the 'Monad' @m@.
--
-- The 'inferContext' method represents the following constraints on @t@:
--
-- * @HNodesConstraint (InferOf t) (Unify m)@ - The child nodes of the inferrence can unify in the @m@ 'Monad'
-- * @HNodesConstraint t (Infer m)@ - @Infer m@ is also available for child nodes
--
-- It replaces context for the 'Infer' class to avoid @UndecidableSuperClasses@.
--
-- Instances usually don't need to implement this method as the default implementation works for them,
-- but infinitely polymorphic trees such as 'Hyper.Type.AST.NamelessScope.Scope' do need to implement the method,
-- because the required context is infinite.
class (Monad m, HFunctor t) => Infer m t where
    -- | Infer the body of an expression given the inference actions for its child nodes.
    inferBody ::
        t # InferChild m h ->
        m (t # h, InferOf t # UVarOf m)
    default inferBody ::
        (Generic1 t, Infer m (Rep1 t), InferOf t ~ InferOf (Rep1 t)) =>
        t # InferChild m h ->
        m (t # h, InferOf t # UVarOf m)
    inferBody =
        fmap (Lens._1 %~ to1) . inferBody . from1

    -- TODO: Putting documentation here causes duplication in the haddock documentation
    inferContext ::
        proxy0 m ->
        proxy1 t ->
        Dict (HNodesConstraint t (Infer m), HNodesConstraint (InferOf t) (UnifyGen m))
    {-# INLINE inferContext #-}
    default inferContext ::
        (HNodesConstraint t (Infer m), HNodesConstraint (InferOf t) (UnifyGen m)) =>
        proxy0 m ->
        proxy1 t ->
        Dict (HNodesConstraint t (Infer m), HNodesConstraint (InferOf t) (UnifyGen m))
    inferContext _ _ = Dict

instance Recursive (Infer m) where
    {-# INLINE recurse #-}
    recurse p = Dict \\ inferContext (Proxy @m) (proxyArgument p)

type instance InferOf (a :+: _) = InferOf a

instance (InferOf a ~ InferOf b, Infer m a, Infer m b) => Infer m (a :+: b) where
    {-# INLINE inferBody #-}
    inferBody (L1 x) = inferBody x <&> Lens._1 %~ L1
    inferBody (R1 x) = inferBody x <&> Lens._1 %~ R1

    {-# INLINE inferContext #-}
    inferContext p _ = Dict \\ inferContext p (Proxy @a) \\ inferContext p (Proxy @b)

type instance InferOf (M1 _ _ h) = InferOf h

instance Infer m h => Infer m (M1 i c h) where
    {-# INLINE inferBody #-}
    inferBody (M1 x) = inferBody x <&> Lens._1 %~ M1

    {-# INLINE inferContext #-}
    inferContext p _ = Dict \\ inferContext p (Proxy @h)

type instance InferOf (Rec1 h) = InferOf h

instance Infer m h => Infer m (Rec1 h) where
    {-# INLINE inferBody #-}
    inferBody (Rec1 x) = inferBody x <&> Lens._1 %~ Rec1

    {-# INLINE inferContext #-}
    inferContext p _ = Dict \\ inferContext p (Proxy @h)
