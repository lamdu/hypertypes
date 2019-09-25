-- | Generalization of type schemes

{-# LANGUAGE UndecidableInstances, TemplateHaskell, FlexibleInstances #-}

module Hyper.Unify.Generalize
    ( generalize, instantiate

    , GTerm(..), _GMono, _GPoly, _GBody, HWitness(..)

    , instantiateWith, instantiateForAll

    , -- | Exports for @SPECIALIZE@ pragmas.
      instantiateH
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Writer (WriterT(..), tell)
import           Data.Constraint (withDict)
import           Data.Monoid (All(..))
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Hyper
import           Hyper.Class.Traversable
import           Hyper.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           Hyper.Recurse
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Type.Combinator.Flip
import           Hyper.Unify.Constraints
import           Hyper.Unify.Lookup (semiPruneLookup)
import           Hyper.Unify.New
import           Hyper.Unify.Occurs (occursError)
import           Hyper.Unify.Term (UTerm(..), uBody)

import           Prelude.Compat

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
    | GBody (ast # GTerm v) -- ^ Term with some polymorphic parts
    deriving Generic

Lens.makePrisms ''GTerm
makeCommonInstances [''GTerm]

instance RNodes a => HNodes (Flip GTerm a) where
    type HNodesConstraint (Flip GTerm a) c = (c a, Recursive c)
    data HWitness (Flip GTerm a) n = E_Flip_GTerm (HRecWitness a n)
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (E_Flip_GTerm HRecSelf) = const id
    kLiftConstraint (E_Flip_GTerm (HRecSub c n)) = kLiftConstraintH c n

kLiftConstraintH ::
    forall a c b n r.
    (RNodes a, HNodesConstraint (Flip GTerm a) c) =>
    HWitness a b -> HRecWitness b n -> Proxy c -> (c n => r) -> r
kLiftConstraintH c n =
    withDict (recurse (Proxy @(RNodes a))) $
    withDict (recurse (Proxy @(c a))) $
    kLiftConstraint c (Proxy @RNodes)
    ( kLiftConstraint c (Proxy @c)
        (kLiftConstraint (E_Flip_GTerm n))
    )

instance Recursively HFunctor ast => HFunctor (Flip GTerm ast) where
    {-# INLINE mapH #-}
    mapH f =
        _Flip %~
        \case
        GMono x -> f (E_Flip_GTerm HRecSelf) x & GMono
        GPoly x -> f (E_Flip_GTerm HRecSelf) x & GPoly
        GBody x ->
            withDict (recursively (Proxy @(HFunctor ast))) $
            mapH
            ( \cw ->
                kLiftConstraint cw (Proxy @(Recursively HFunctor)) $
                Lens.from _Flip %~
                mapH (f . (\(E_Flip_GTerm nw) -> E_Flip_GTerm (HRecSub cw nw)))
            ) x
            & GBody

instance Recursively HFoldable ast => HFoldable (Flip GTerm ast) where
    {-# INLINE foldMapH #-}
    foldMapH f =
        \case
        GMono x -> f (E_Flip_GTerm HRecSelf) x
        GPoly x -> f (E_Flip_GTerm HRecSelf) x
        GBody x ->
            withDict (recursively (Proxy @(HFoldable ast))) $
            foldMapH
            ( \cw ->
                kLiftConstraint cw (Proxy @(Recursively HFoldable)) $
                foldMapH (f . (\(E_Flip_GTerm nw) -> E_Flip_GTerm (HRecSub cw nw)))
                . (_Flip #)
            ) x
        . (^. _Flip)

instance RTraversable ast => HTraversable (Flip GTerm ast) where
    {-# INLINE sequenceH #-}
    sequenceH (MkFlip fx) =
        case fx of
        GMono x -> runContainedH x <&> GMono
        GPoly x -> runContainedH x <&> GPoly
        GBody x ->
            withDict (recurse (Proxy @(RTraversable ast))) $
            -- HTraversable will be required when not implied by Recursively
            traverseH
            ( Proxy @RTraversable #> Lens.from _Flip sequenceH
            ) x
            <&> GBody
        <&> MkFlip

-- | Generalize a unification term pointed by the given variable to a `GTerm`.
-- Unification variables that are scoped within the term
-- become universally quantified skolems.
generalize ::
    forall m t.
    Unify m t =>
    Tree (UVarOf m) t -> m (Tree (GTerm (UVarOf m)) t)
generalize v0 =
    do
        (v1, u) <- semiPruneLookup v0
        c <- scopeConstraints
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
                withDict (unifyRecursive (Proxy @m) (Proxy @t)) $
                do
                    bindVar binding v1 (UResolving t)
                    r <- traverseH (Proxy @(Unify m) #> generalize) (t ^. uBody)
                    r <$ bindVar binding v1 (UTerm t)
                <&>
                \b ->
                if foldMapH (Proxy @(Unify m) #> All . Lens.has _GMono) b ^. Lens._Wrapped
                then GMono v1
                else GBody b
            UResolving t -> GMono v1 <$ occursError v1 t
            _ -> pure (GMono v1)

{-# INLINE instantiateForAll #-}
instantiateForAll ::
    Unify m t =>
    (TypeConstraintsOf t -> Tree (UTerm (UVarOf m)) t) ->
    Tree (UVarOf m) t ->
    WriterT [m ()] m (Tree (UVarOf m) t)
instantiateForAll cons x =
    lookupVar binding x & lift
    >>=
    \case
    USkolem l ->
        do
            tell [bindVar binding x (USkolem l)]
            r <- scopeConstraints <&> (<> l) >>= newVar binding . cons & lift
            UInstantiated r & bindVar binding x & lift
            pure r
    UInstantiated v -> pure v
    _ -> error "unexpected state at instantiate's forall"

-- TODO: Better name?
{-# INLINE instantiateH #-}
instantiateH ::
    forall m t.
    Unify m t =>
    (forall n. TypeConstraintsOf n -> Tree (UTerm (UVarOf m)) n) ->
    Tree (GTerm (UVarOf m)) t ->
    WriterT [m ()] m (Tree (UVarOf m) t)
instantiateH _ (GMono x) = pure x
instantiateH cons (GPoly x) = instantiateForAll cons x
instantiateH cons (GBody x) =
    withDict (unifyRecursive (Proxy @m) (Proxy @t)) $
    traverseH (Proxy @(Unify m) #> instantiateH cons) x >>= lift . newTerm

{-# INLINE instantiateWith #-}
instantiateWith ::
    forall m t a.
    Unify m t =>
    m a ->
    (forall n. TypeConstraintsOf n -> Tree (UTerm (UVarOf m)) n) ->
    Tree (GTerm (UVarOf m)) t ->
    m (Tree (UVarOf m) t, a)
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
    Unify m t =>
    Tree (GTerm (UVarOf m)) t -> m (Tree (UVarOf m) t)
instantiate g = instantiateWith (pure ()) UUnbound g <&> (^. Lens._1)