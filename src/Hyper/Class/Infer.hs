{-# LANGUAGE TemplateHaskell, DefaultSignatures, FlexibleInstances #-}

module Hyper.Class.Infer
    ( InferOf
    , Infer(..)
    , InferChild(..), _InferChild
    , InferredChild(..), inType, inRep
    ) where

import           Hyper
import           Hyper.Class.Unify
import           Hyper.Recurse
import           Control.Lens (makeLenses, makePrisms)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint (Dict(..), withDict)
import           Data.Functor.Sum.PolyKinds (Sum(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

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

type instance InferOf (Sum a b) = InferOf a

-- | A 'AHyperType' containing an inferred child node
data InferredChild v k t = InferredChild
    { _inRep :: !(k t)
        -- ^ Inferred node.
        --
        -- An 'inferBody' implementation needs to place this value in the corresponding child node of the inferred term body
    , _inType :: !(Tree (InferOf (GetHyperType t)) v)
        -- ^ The inference result for the child node.
        --
        -- An 'inferBody' implementation may use it to perform unifications with it.
    }
makeLenses ''InferredChild

-- | A 'AHyperType' containing an inference action.
--
-- The caller may modify the scope before invoking the action via
-- 'Hyper.Class.Infer.Env.localScopeType' or 'Hyper.Infer.ScopeLevel.localLevel'
newtype InferChild m k t =
    InferChild { inferChild :: m (InferredChild (UVarOf m) k t) }
makePrisms ''InferChild

-- | @Infer m t@ enables 'Hyper.Infer.infer' to perform type-inference for @t@ in the 'Monad' @m@.
--
-- The 'inferContext' method represents the following constraints on @t@:
--
-- * @KNodesConstraint (InferOf t) (Unify m)@ - The child nodes of the inferrence can unify in the @m@ 'Monad'
-- * @KNodesConstraint t (Infer m)@ - @Infer m@ is also available for child nodes
--
-- It replaces context for the 'Infer' class to avoid @UndecidableSuperClasses@.
--
-- Instances usually don't need to implement this method as the default implementation works for them,
-- but infinitely polymorphic trees such as 'Hyper.Type.AST.NamelessScope.Scope' do need to implement the method,
-- because the required context is infinite.
class (Monad m, KFunctor t) => Infer m t where
    -- | Infer the body of an expression given the inference actions for its child nodes.
    inferBody ::
        Tree t (InferChild m k) ->
        m (Tree t k, Tree (InferOf t) (UVarOf m))

    -- TODO: Putting documentation here causes duplication in the haddock documentation
    inferContext ::
        Proxy m ->
        Proxy t ->
        Dict (KNodesConstraint t (Infer m), KNodesConstraint (InferOf t) (Unify m))
    {-# INLINE inferContext #-}
    default inferContext ::
        (KNodesConstraint t (Infer m), KNodesConstraint (InferOf t) (Unify m)) =>
        Proxy m ->
        Proxy t ->
        Dict (KNodesConstraint t (Infer m), KNodesConstraint (InferOf t) (Unify m))
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

instance (InferOf a ~ InferOf b, Infer m a, Infer m b) => Infer m (Sum a b) where
    {-# INLINE inferBody #-}
    inferBody (InL x) = inferBody x <&> Lens._1 %~ InL
    inferBody (InR x) = inferBody x <&> Lens._1 %~ InR

    {-# INLINE inferContext #-}
    inferContext p _ =
        withDict (inferContext p (Proxy @a)) $
        withDict (inferContext p (Proxy @b)) Dict
