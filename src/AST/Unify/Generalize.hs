{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, LambdaCase, InstanceSigs #-}
{-# LANGUAGE RankNTypes, TupleSections, FlexibleInstances, DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}

module AST.Unify.Generalize
    ( generalize, instantiate

    , -- TODO: should these not be exported? (Internals)
      -- Exported also for specialization
      instantiateWith, instantiateForAll, instantiateH
    , GTerm(..), _GMono, _GPoly, _GBody
    ) where

import           Algebra.Lattice (JoinSemiLattice(..))
import           Algebra.PartialOrd (PartialOrd(..))
import           AST
import           AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import           AST.Knot.Flip (Flip(..), _Flip)
import           AST.Unify
import           AST.Unify.Term (UTerm(..), uBody)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Writer (WriterT(..), tell)
import           Data.Binary (Binary)
import           Data.Constraint (Constraint, withDict)
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
    | GBody (Tie ast (GTerm v)) -- ^ Term with some polymorphic parts
    deriving Generic
Lens.makePrisms ''GTerm
makeChildren ''GTerm

instance Children (Flip GTerm ast) where
    type ChildrenConstraint (Flip GTerm ast) cls = Recursive cls ast
    {-# INLINE children #-}
    children ::
        forall f constraint n m.
        (Applicative f, Recursive constraint ast) =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child -> f (Tree m child)) ->
        Tree (Flip GTerm ast) n -> f (Tree (Flip GTerm ast) m)
    children p f (Flip g) =
        case g of
        GMono x -> f x <&> GMono
        GPoly x -> f x <&> GPoly
        GBody x ->
            recursiveChildren p (Lens.from _Flip (children p f)) x
            <&> GBody
        <&> Flip

-- | Generalize a unification term pointed by the given variable to a `GTerm`.
-- Unification variables that are scoped within the term
-- become universally quantified skolems.
generalize ::
    forall m t.
    Recursive (Unify m) t =>
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
                withDict (recursive :: RecursiveDict (Unify m) t) $
                do
                    bindVar binding v1 (UResolving t)
                    r <- children p generalize (t ^. uBody)
                    r <$ bindVar binding v1 (UTerm t)
                <&>
                \b ->
                if foldMapChildren p (All . Lens.has _GMono) b ^. Lens._Wrapped
                then GMono v1
                else GBody b
            UResolving t -> GMono v1 <$ occursError v1 t
            _ -> pure (GMono v1)
    where
        p = Proxy :: Proxy (Recursive (Unify m))

{-# INLINE instantiateForAll #-}
instantiateForAll ::
    Unify m t =>
    (TypeConstraintsOf t -> Tree (UTerm (UVarOf m)) t) ->
    Tree (UVarOf m) t -> WriterT [m ()] m (Tree (UVarOf m) t)
instantiateForAll cons x =
    lookupVar binding x & lift
    >>=
    \case
    USkolem l ->
        do
            tell [bindVar binding x (USkolem l)]
            r <- scopeConstraints <&> (\/ l) >>= newVar binding . cons & lift
            UInstantiated r & bindVar binding x & lift
            pure r
    UInstantiated v -> pure v
    _ -> error "unexpected state at instantiate's forall"

-- TODO: Better name?
{-# INLINE instantiateH #-}
instantiateH ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (GTerm (UVarOf m)) t -> WriterT [m ()] m (Tree (UVarOf m) t)
instantiateH (GMono x) = pure x
instantiateH (GBody x) =
    recursiveChildren (Proxy :: Proxy (Unify m)) instantiateH x >>= lift . newTerm
instantiateH (GPoly x) = instantiateForAll UUnbound x

{-# INLINE instantiateWith #-}
instantiateWith ::
    Recursive (Unify m) t =>
    m a ->
    Tree (GTerm (UVarOf m)) t ->
    m (Tree (UVarOf m) t, a)
instantiateWith action g =
    do
        (r, recover) <- runWriterT (instantiateH g)
        action <* sequence_ recover <&> (r, )

-- | Instantiate a `Generalized` type with fresh unification variables
-- for the quantified variables
{-# INLINE instantiate #-}
instantiate ::
    Recursive (Unify m) t =>
    Tree (GTerm (UVarOf m)) t -> m (Tree (UVarOf m) t)
instantiate g = instantiateWith (pure ()) g <&> (^. Lens._1)

type Deps c v t = ((c (v t), c (Tie t (GTerm v))) :: Constraint)
deriving instance Deps Eq   v t => Eq   (GTerm v t)
deriving instance Deps Ord  v t => Ord  (GTerm v t)
deriving instance Deps Show v t => Show (GTerm v t)
instance Deps Binary v t => Binary (GTerm v t)
instance Deps NFData v t => NFData (GTerm v t)
