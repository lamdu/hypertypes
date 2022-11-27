{-# LANGUAGE FlexibleContexts #-}

module Hyper.Infer
    ( infer
    , InferResultsConstraint
    , inferUVarsApplyBindings
    , module Hyper.Class.Infer
    , module Hyper.Class.Infer.Env
    , module Hyper.Class.Infer.InferOf
    , module Hyper.Infer.ScopeLevel
    , module Hyper.Infer.Result
      -- | Exported only for SPECIALIZE pragmas
    , inferH
    ) where

import qualified Control.Lens as Lens
import Hyper
import Hyper.Class.Infer
import Hyper.Class.Infer.Env
import Hyper.Class.Infer.InferOf
import Hyper.Class.Nodes (HNodesHaveConstraint (..))
import Hyper.Infer.Result
import Hyper.Infer.ScopeLevel
import Hyper.Unify (UVarOf, Unify, applyBindings)

import Hyper.Internal.Prelude

-- | Perform Hindley-Milner type inference of a term
{-# INLINE infer #-}
infer ::
    forall m t a.
    Infer m t =>
    Ann a # t ->
    m (Ann (a :*: InferResult (UVarOf m)) # t)
infer (Ann a x) =
    inferBody (hmap (Proxy @(Infer m) #> inferH) x)
        <&> (\(xI, t) -> Ann (a :*: InferResult t) xI)
            \\ inferContext (Proxy @m) (Proxy @t)

{-# INLINE inferH #-}
inferH ::
    Infer m t =>
    Ann a # t ->
    InferChild m (Ann (a :*: InferResult (UVarOf m))) # t
inferH c = infer c <&> (\i -> InferredChild i (i ^. hAnn . Lens._2 . _InferResult)) & InferChild

type InferResultsConstraint c = Recursively (InferOfConstraint (HNodesHaveConstraint c))

inferUVarsApplyBindings ::
    forall m t a.
    ( Applicative m
    , RTraversable t
    , Recursively (InferOfConstraint HTraversable) t
    , InferResultsConstraint (Unify m) t
    ) =>
    Ann (a :*: InferResult (UVarOf m)) # t ->
    m (Ann (a :*: InferResult (Pure :*: UVarOf m)) # t)
inferUVarsApplyBindings =
    htraverseFlipped $
        Proxy @(Recursively (InferOfConstraint HTraversable)) #*#
            Proxy @(InferResultsConstraint (Unify m)) #>
                Lens._2 f
    where
        f ::
            forall n.
            ( Recursively (InferOfConstraint HTraversable) n
            , InferResultsConstraint (Unify m) n
            ) =>
            InferResult (UVarOf m) # n ->
            m (InferResult (Pure :*: UVarOf m) # n)
        f =
            htraverseFlipped (Proxy @(Unify m) #> \x -> applyBindings x <&> (:*: x))
                \\ inferOfConstraint @HTraversable (Proxy @n)
                \\ recursively (Proxy @(InferOfConstraint HTraversable n))
                \\ hNodesHaveConstraint (Proxy @(Unify m)) (Proxy @(InferOf n))
                \\ inferOfConstraint @(HNodesHaveConstraint (Unify m)) (Proxy @n)
                \\ recursively (Proxy @(InferOfConstraint (HNodesHaveConstraint (Unify m)) n))
