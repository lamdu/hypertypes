{-# LANGUAGE UndecidableInstances, TemplateHaskell, RankNTypes, FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module AST.Unify.Generalize
    ( generalize, instantiate

    , -- TODO: should these not be exported? (Internals)
      -- Exported also for specialization
      instantiateWith, instantiateForAll, instantiateH
    , GTerm(..), _GMono, _GPoly, _GBody, KWitness(..)
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import           AST
import           AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           AST.Class.Recursive
import           AST.Class.Traversable
import           AST.Combinator.Flip
import           AST.TH.Internal.Instances (makeCommonInstances)
import           AST.Unify.Constraints
import           AST.Unify.Lookup (semiPruneLookup)
import           AST.Unify.New
import           AST.Unify.Occurs (occursError)
import           AST.Unify.Term (UTerm(..), uBody)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Writer (WriterT(..), tell)
import           Data.Constraint (Dict(..), withDict)
import           Data.Monoid (All(..))
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)

import           Prelude.Compat

-- | An efficient representation of a type scheme arising from
-- generalizing a unification term. Type subexpressions which are
-- completely monomoprhic are tagged as such, to avoid redundant
-- instantation and unification work
data GTerm v ast
    = GMono (v ast) -- ^ Completely monomoprhic term
    | GPoly (v ast)
        -- ^ Points to a quantified variable (instantiation will
        -- create fresh unification terms) (`AST.Unify.Term.USkolem`
        -- or `AST.Unify.Term.UResolved`)
    | GBody (Node ast (GTerm v)) -- ^ Term with some polymorphic parts
    deriving Generic

Lens.makePrisms ''GTerm
makeCommonInstances [''GTerm]

instance RNodes a => KNodes (Flip GTerm a) where
    type NodesConstraint (Flip GTerm a) c = (c a, Recursive c)
    data KWitness (Flip GTerm a) n = KWitness_Flip_GTerm (KRecWitness a n)
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (KWitness_Flip_GTerm KRecSelf) = const id
    kLiftConstraint (KWitness_Flip_GTerm (KRecSub c n)) = kLiftConstraintH c n
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = Dict

kLiftConstraintH ::
    forall a c b n r.
    (RNodes a, NodesConstraint (Flip GTerm a) c) =>
    KWitness a b -> KRecWitness b n -> Proxy c -> (c n => r) -> r
kLiftConstraintH c n =
    withDict (recurseBoth (Proxy @(And RNodes c a))) $
    kLiftConstraint c (Proxy @(And RNodes c))
    (kLiftConstraint (KWitness_Flip_GTerm n))

instance RFunctor ast => KFunctor (Flip GTerm ast) where
    {-# INLINE mapK #-}
    mapK f =
        _Flip %~
        \case
        GMono x -> f (KWitness_Flip_GTerm KRecSelf) x & GMono
        GPoly x -> f (KWitness_Flip_GTerm KRecSelf) x & GPoly
        GBody x ->
            withDict (recurse (Proxy @(RFunctor ast))) $
            mapK
            ( \cw ->
                kLiftConstraint cw (Proxy @RFunctor) $
                Lens.from _Flip %~
                mapK (f . (\(KWitness_Flip_GTerm nw) -> KWitness_Flip_GTerm (KRecSub cw nw)))
            ) x
            & GBody

instance RFoldable ast => KFoldable (Flip GTerm ast) where
    {-# INLINE foldMapK #-}
    foldMapK f =
        \case
        GMono x -> f (KWitness_Flip_GTerm KRecSelf) x
        GPoly x -> f (KWitness_Flip_GTerm KRecSelf) x
        GBody x ->
            withDict (recurse (Proxy @(RFoldable ast))) $
            foldMapK
            ( \cw ->
                kLiftConstraint cw (Proxy @RFoldable) $
                foldMapK (f . (\(KWitness_Flip_GTerm nw) -> KWitness_Flip_GTerm (KRecSub cw nw)))
                . (_Flip #)
            ) x
        . (^. _Flip)

instance RTraversable ast => KTraversable (Flip GTerm ast) where
    {-# INLINE sequenceK #-}
    sequenceK (MkFlip fx) =
        case fx of
        GMono x -> runContainedK x <&> GMono
        GPoly x -> runContainedK x <&> GPoly
        GBody x ->
            withDict (recurse (Proxy @(RTraversable ast))) $
            -- KTraversable will be required when not implied by Recursively
            traverseKWith (Proxy @RTraversable)
            (Lens.from _Flip sequenceK) x
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
                    r <- traverseKWith (Proxy @(Unify m)) generalize (t ^. uBody)
                    r <$ bindVar binding v1 (UTerm t)
                <&>
                \b ->
                if foldMapKWith (Proxy @(Unify m)) (All . Lens.has _GMono) b ^. Lens._Wrapped
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
    traverseKWith (Proxy @(Unify m)) (instantiateH cons) x >>= lift . newTerm

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
