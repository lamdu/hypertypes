-- | Generalization of type schemes

{-# LANGUAGE UndecidableInstances, TemplateHaskell, FlexibleContexts, FlexibleInstances #-}

module Hyper.Unify.Generalize
    ( generalize, instantiate

    , GTerm(..), _GMono, _GPoly, _GBody, W_GTerm(..)

    , instantiateWith, instantiateForAll

    , -- | Exports for @SPECIALIZE@ pragmas.
      instantiateH
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import qualified Control.Lens as Lens
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Writer (WriterT(..), tell)
import           Data.Monoid (All(..))
import           Hyper
import           Hyper.Class.Traversable
import           Hyper.Class.Unify
import           Hyper.Recurse
import           Hyper.Unify.Constraints
import           Hyper.Unify.New (newTerm)
import           Hyper.Unify.Term (UTerm(..), uBody)

import           Hyper.Internal.Prelude

-- | An efficient representation of a type scheme arising from
-- generalizing a unification term. Type subexpressions which are
-- completely monomoprhic are tagged as such, to avoid redundant
-- instantation and unification work
data GTerm v ast
    = GMono (v ast) -- ^ Completely monomoprhic term
    | GPoly (v ast)
        -- ^ Points to a quantified variable (instantiation will
        -- create fresh unification terms) (`Hyper.Unify.Term.USkolem`
        -- or `Hyper.Unify.Term.UResolved`)
    | GBody (ast :# GTerm v) -- ^ Term with some polymorphic parts
    deriving Generic

makePrisms ''GTerm
makeCommonInstances [''GTerm]
makeHTraversableAndBases ''GTerm

instance RNodes a => HNodes (HFlip GTerm a) where
    type HNodesConstraint (HFlip GTerm a) c = (c a, Recursive c)
    type HWitnessType (HFlip GTerm a) = HRecWitness a
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (HWitness HRecSelf) = \_ x -> x
    hLiftConstraint (HWitness (HRecSub c n)) = hLiftConstraintH c n

hLiftConstraintH ::
    forall a c b n r.
    (RNodes a, HNodesConstraint (HFlip GTerm a) c) =>
    HWitness a b -> HRecWitness b n -> Proxy c -> (c n => r) -> r
hLiftConstraintH c n p f =
    withDict (recurse (Proxy @(RNodes a))) $
    withDict (recurse (Proxy @(c a))) $
    hLiftConstraint c (Proxy @RNodes)
    ( hLiftConstraint c p
        (hLiftConstraint (HWitness @(HFlip GTerm _) n) p f)
    )

instance Recursively HFunctor ast => HFunctor (HFlip GTerm ast) where
    {-# INLINE hmap #-}
    hmap f =
        _HFlip %~
        \case
        GMono x -> f (HWitness HRecSelf) x & GMono
        GPoly x -> f (HWitness HRecSelf) x & GPoly
        GBody x ->
            withDict (recursively (Proxy @(HFunctor ast))) $
            hmap
            ( \cw ->
                hLiftConstraint cw (Proxy @(Recursively HFunctor)) $
                hflipped %~
                hmap (f . (\(HWitness nw) -> HWitness (HRecSub cw nw)))
            ) x
            & GBody

instance Recursively HFoldable ast => HFoldable (HFlip GTerm ast) where
    {-# INLINE hfoldMap #-}
    hfoldMap f =
        \case
        GMono x -> f (HWitness HRecSelf) x
        GPoly x -> f (HWitness HRecSelf) x
        GBody x ->
            withDict (recursively (Proxy @(HFoldable ast))) $
            hfoldMap
            ( \cw ->
                hLiftConstraint cw (Proxy @(Recursively HFoldable)) $
                hfoldMap (f . (\(HWitness nw) -> HWitness (HRecSub cw nw)))
                . (_HFlip #)
            ) x
        . (^. _HFlip)

instance RTraversable ast => HTraversable (HFlip GTerm ast) where
    {-# INLINE hsequence #-}
    hsequence =
        \case
        GMono x -> runContainedH x <&> GMono
        GPoly x -> runContainedH x <&> GPoly
        GBody x ->
            withDict (recurse (Proxy @(RTraversable ast))) $
            -- HTraversable will be required when not implied by Recursively
            htraverse (Proxy @RTraversable #> hflipped hsequence) x
            <&> GBody
        & _HFlip

-- | Generalize a unification term pointed by the given variable to a `GTerm`.
-- Unification variables that are scoped within the term
-- become universally quantified skolems.
generalize ::
    forall m t.
    UnifyGen m t =>
    UVarOf m # t -> m (GTerm (UVarOf m) # t)
generalize v0 =
    do
        (v1, u) <- semiPruneLookup v0
        c <- scopeConstraints (Proxy @t)
        case u of
            UUnbound l | toScopeConstraints l `leq` c ->
                GPoly v1 <$
                -- We set the variable to a skolem,
                -- so additional unifications after generalization
                -- (for example hole resumptions where supported)
                -- cannot unify it with anything.
                bindVar binding v1 (USkolem (generalizeConstraints l))
            USkolem l | toScopeConstraints l `leq` c -> pure (GPoly v1)
            UTerm t ->
                withDict (unifyGenRecursive (Proxy @m) (Proxy @t)) $
                do
                    bindVar binding v1 (UResolving t)
                    r <- htraverse (Proxy @(UnifyGen m) #> generalize) (t ^. uBody)
                    r <$ bindVar binding v1 (UTerm t)
                <&>
                \b ->
                if hfoldMap (Proxy @(UnifyGen m) #> All . Lens.has _GMono) b ^. Lens._Wrapped
                then GMono v1
                else GBody b
            UResolving t -> GMono v1 <$ occursError v1 t
            _ -> pure (GMono v1)

{-# INLINE instantiateForAll #-}
instantiateForAll ::
    forall m t. UnifyGen m t =>
    (TypeConstraintsOf t -> UTerm (UVarOf m) # t) ->
    UVarOf m # t ->
    WriterT [m ()] m (UVarOf m # t)
instantiateForAll cons x =
    lookupVar binding x & lift
    >>=
    \case
    USkolem l ->
        do
            tell [bindVar binding x (USkolem l)]
            r <- scopeConstraints (Proxy @t) <&> (<> l) >>= newVar binding . cons & lift
            UInstantiated r & bindVar binding x & lift
            pure r
    UInstantiated v -> pure v
    _ -> error "unexpected state at instantiate's forall"

-- TODO: Better name?
{-# INLINE instantiateH #-}
instantiateH ::
    forall m t.
    UnifyGen m t =>
    (forall n. TypeConstraintsOf n -> UTerm (UVarOf m) # n) ->
    GTerm (UVarOf m) # t ->
    WriterT [m ()] m (UVarOf m # t)
instantiateH _ (GMono x) = pure x
instantiateH cons (GPoly x) = instantiateForAll cons x
instantiateH cons (GBody x) =
    withDict (unifyGenRecursive (Proxy @m) (Proxy @t)) $
    htraverse (Proxy @(UnifyGen m) #> instantiateH cons) x >>= lift . newTerm

{-# INLINE instantiateWith #-}
instantiateWith ::
    forall m t a.
    UnifyGen m t =>
    m a ->
    (forall n. TypeConstraintsOf n -> UTerm (UVarOf m) # n) ->
    GTerm (UVarOf m) # t ->
    m (UVarOf m # t, a)
instantiateWith action cons g =
    do
        (r, recover) <-
            instantiateH cons g
            & runWriterT
        action <* sequence_ recover <&> (r, )

-- | Instantiate a generalized type with fresh unification variables
-- for the quantified variables
{-# INLINE instantiate #-}
instantiate ::
    UnifyGen m t =>
    GTerm (UVarOf m) # t -> m (UVarOf m # t)
instantiate g = instantiateWith (pure ()) UUnbound g <&> (^. Lens._1)
