{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, LambdaCase, InstanceSigs #-}
{-# LANGUAGE RankNTypes, TupleSections #-}

module AST.Unify.Generalize
    ( Generalized(..), _Generalized
    , generalize, monomorphic, instantiate

    , -- TODO: should these not be exported? (Internals)
      -- Exported also for specialization
      instantiateWith, instantiateH
    , GTerm(..), _GMono, _GPoly, _GBody
    ) where

import           Algebra.Lattice (JoinSemiLattice(..))
import           Algebra.PartialOrd (PartialOrd(..))
import           AST
import           AST.Class.Unify (Unify(..), UVar)
import           AST.Unify (newTerm, semiPruneLookup)
import           AST.Unify.Binding (Binding(..))
import           AST.Unify.Constraints (TypeConstraints(..), MonadScopeConstraints(..))
import           AST.Unify.Term (UTerm(..), uBody)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Writer (WriterT(..), tell)
import           Data.Constraint (withDict)
import           Data.Monoid (All(..))
import           Data.Proxy (Proxy(..))

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
    | GBody (Tie ast (GTerm v)) -- ^ Term with some polymorphic parts
Lens.makePrisms ''GTerm
makeChildren ''GTerm

-- | Wrapper for `GTerm` whose children are all the pointed
-- unification terms in the entire GTerm ast (all monomorphic terms
-- and the quantified variables).
newtype Generalized ast v = Generalized (Tree (GTerm (RunKnot v)) ast)
Lens.makePrisms ''Generalized

instance Children (Generalized ast) where
    type ChildrenConstraint (Generalized ast) cls = Recursive cls ast
    {-# INLINE children #-}
    children ::
        forall f constraint n m.
        (Applicative f, Recursive constraint ast) =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child -> f (Tree m child)) ->
        Tree (Generalized ast) n -> f (Tree (Generalized ast) m)
    children p f (Generalized g) =
        case g of
        GMono x -> f x <&> GMono
        GPoly x -> f x <&> GPoly
        GBody x ->
            recursiveChildren p (Lens.from _Generalized (children p f)) x
            <&> GBody
        <&> Generalized

-- | Generalize a unification term pointed by the given variable to a
-- `Generalized` term. Unification variables that are scoped within
-- the term become universally quantified skolems.
generalize ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UVar m) t -> m (Tree (Generalized t) (UVar m))
generalize v0 =
    do
        (v1, u) <- semiPruneLookup v0
        c <- scopeConstraints
        case u of
            UUnbound l | l `leq` c ->
                GPoly v1 <$
                -- We set the variable to a skolem,
                -- so additional unifications after generalization
                -- (for example hole resumptions where supported)
                -- cannot unify it with anything.
                bindVar binding v1 (USkolem (generalizeConstraints l))
            USkolem l | l `leq` c -> pure (GPoly v1)
            UTerm t ->
                withDict (recursive :: RecursiveDict (Unify m) t) $
                children p (fmap (^. _Generalized) . generalize) (t ^. uBody)
                <&>
                \b ->
                if foldMapChildren p (All . Lens.has _GMono) b ^. Lens._Wrapped
                then GMono v1
                else GBody b
            _ -> pure (GMono v1)
    <&> Generalized
    where
        p = Proxy :: Proxy (Recursive (Unify m))

-- | Lift a monomorphic type term into `Generalized`
{-# INLINE monomorphic #-}
monomorphic :: Tree v t -> Tree (Generalized t) v
monomorphic = Generalized . GMono

-- TODO: Better name?
{-# INLINE instantiateH #-}
instantiateH ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (GTerm (UVar m)) t -> WriterT [m ()] m (Tree (UVar m) t)
instantiateH (GMono x) = pure x
instantiateH (GBody x) =
    recursiveChildren (Proxy :: Proxy (Unify m)) instantiateH x >>= lift . newTerm
instantiateH (GPoly x) =
    lookupVar binding x & lift
    >>=
    \case
    USkolem l ->
        do
            tell [bindVar binding x (USkolem l)]
            r <- scopeConstraints <&> (\/ l) >>= newVar binding . UUnbound & lift
            UInstantiated r & bindVar binding x & lift
            pure r
    UInstantiated v -> pure v
    _ -> error "unexpected state at instantiate's forall"

{-# INLINE instantiateWith #-}
instantiateWith ::
    Recursive (Unify m) t =>
    m a ->
    Tree (Generalized t) (UVar m) ->
    m (Tree (UVar m) t, a)
instantiateWith action (Generalized g) =
    do
        (r, recover) <- runWriterT (instantiateH g)
        action <* sequence_ recover <&> (r, )

-- | Instantiate a `Generalized` type with fresh unification variables
-- for the quantified variables
{-# INLINE instantiate #-}
instantiate ::
    Recursive (Unify m) t =>
    Tree (Generalized t) (UVar m) -> m (Tree (UVar m) t)
instantiate g = instantiateWith (pure ()) g <&> (^. Lens._1)
