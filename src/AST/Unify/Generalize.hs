{-# LANGUAGE UndecidableInstances, TemplateHaskell, RankNTypes, FlexibleInstances #-}

module AST.Unify.Generalize
    ( generalize, instantiate

    , -- TODO: should these not be exported? (Internals)
      -- Exported also for specialization
      instantiateWith, instantiateForAll, instantiateH
    , GTerm(..), _GMono, _GPoly, _GBody
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import           AST
import           AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           AST.Class.Recursive
import           AST.Class.Traversable
import           AST.Combinator.Flip
import           AST.Unify
import           AST.Unify.Lookup (semiPruneLookup)
import           AST.Unify.New
import           AST.Unify.Occurs (occursError)
import           AST.Unify.Term (UTerm(..), uBody)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Writer (WriterT(..), tell)
import           Data.Binary (Binary)
import           Data.Constraint (withDict)
import           Data.Monoid (All(..))
import           Data.Proxy (Proxy(..))
import           Generics.OneLiner (Constraints)
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

instance KNodes (Flip GTerm a) where
    type NodesConstraint (Flip GTerm a) c = (c a, Recursive c)
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = id

instance RFunctor ast => KFunctor (Flip GTerm ast) where
    {-# INLINE mapKWith #-}
    mapKWith p f =
        _Flip %~
        \case
        GMono x -> f x & GMono
        GPoly x -> f x & GPoly
        GBody x ->
            recurseBoth (p0 p) $
            mapKWith (p1 p) (Lens.from _Flip %~ mapKWith p f) x
            & GBody
        where
            p0 :: Proxy constraint -> Proxy (And RFunctor constraint ast)
            p0 _ = Proxy
            p1 :: Proxy constraint -> Proxy (And RFunctor constraint)
            p1 _ = Proxy

instance RFoldable ast => KFoldable (Flip GTerm ast) where
    {-# INLINE foldMapKWith #-}
    foldMapKWith p f =
        \case
        GMono x -> f x
        GPoly x -> f x
        GBody x ->
            recurseBoth (p0 p) $
            foldMapKWith (p1 p) (foldMapKWith p f . (_Flip #)) x
        . (^. _Flip)
        where
            p0 :: Proxy constraint -> Proxy (And RFoldable constraint ast)
            p0 _ = Proxy
            p1 :: Proxy constraint -> Proxy (And RFoldable constraint)
            p1 _ = Proxy

instance RTraversable ast => KTraversable (Flip GTerm ast) where
    sequenceK (MkFlip fx) =
        case fx of
        GMono x -> runContainedK x <&> GMono
        GPoly x -> runContainedK x <&> GPoly
        GBody x ->
            withDict (recursiveKTraversable (Proxy @ast)) $
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

-- | Instantiate a `Generalized` type with fresh unification variables
-- for the quantified variables
{-# INLINE instantiate #-}
instantiate ::
    Unify m t =>
    Tree (GTerm (UVarOf m)) t -> m (Tree (UVarOf m) t)
instantiate g = instantiateWith (pure ()) UUnbound g <&> (^. Lens._1)

deriving instance (Constraints (GTerm v t)) Eq   => Eq   (GTerm v t)
deriving instance (Constraints (GTerm v t)) Ord  => Ord  (GTerm v t)
deriving instance (Constraints (GTerm v t)) Show => Show (GTerm v t)
instance (Constraints (GTerm v t)) Binary => Binary (GTerm v t)
instance (Constraints (GTerm v t)) NFData => NFData (GTerm v t)
