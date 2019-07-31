{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, LambdaCase #-}
{-# LANGUAGE RankNTypes, TupleSections, FlexibleInstances, DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances, DataKinds #-}

module AST.Unify.Generalize
    ( generalize, instantiate

    , -- TODO: should these not be exported? (Internals)
      -- Exported also for specialization
      instantiateWith, instantiateForAll, instantiateH
    , GTerm(..), _GMono, _GPoly, _GBody
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import           AST
import           AST.Class
import           AST.Class.Foldable
import           AST.Class.Recursive
import           AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
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
    | GBody (Node ast (GTerm v)) -- ^ Term with some polymorphic parts
    deriving Generic

Lens.makePrisms ''GTerm

instance
    Recursively KNodes ast =>
    KNodes (Flip GTerm ast) where

    type NodeTypesOf (Flip GTerm ast) = RecursiveNodes ast
    type NodesConstraint (Flip GTerm ast) = RecursiveConstraint ast

instance
    (Recursively KNodes ast, Recursively KFunctor ast) =>
    KFunctor (Flip GTerm ast) where

    {-# INLINE mapC #-}
    mapC (RecursiveNodes (MkMapK mapTop) mapSub) =
        _Flip %~
        \case
        GMono x -> mapTop x & GMono
        GPoly x -> mapTop x & GPoly
        GBody x ->
            withDict (recursive :: RecursiveDict ast KNodes) $
            withDict (recursive :: RecursiveDict ast KFunctor) $
            withDict (kNodes (Proxy :: Proxy ast)) $
            mapC
            ( mapKWith (Proxy :: Proxy '[Recursively KNodes, Recursively KFunctor])
                (\(MkFlip f) -> Lens.from _Flip %~ mapC f & MkMapK)
                mapSub
            ) x
            & GBody

instance
    (Recursively KNodes ast, Recursively KFoldable ast) =>
    KFoldable (Flip GTerm ast) where

    {-# INLINE foldMapC #-}
    foldMapC (RecursiveNodes (MkConvertK convTop) convSub) =
        \case
        GMono x -> convTop x
        GPoly x -> convTop x
        GBody x ->
            withDict (recursive :: RecursiveDict ast KNodes) $
            withDict (recursive :: RecursiveDict ast KFoldable) $
            withDict (kNodes (Proxy :: Proxy ast)) $
            foldMapC
            ( mapKWith (Proxy :: Proxy '[Recursively KNodes, Recursively KFoldable])
                (\(MkFlip f) -> foldMapC f . (_Flip #) & MkConvertK)
                convSub
            ) x
        . (^. _Flip)

instance
    ( Recursively KNodes ast
    , Recursively KFunctor ast
    , Recursively KFoldable ast
    , Recursively KTraversable ast
    ) =>
    KTraversable (Flip GTerm ast) where

    sequenceC (MkFlip fx) =
        case fx of
        GMono x -> runContainedK x <&> GMono
        GPoly x -> runContainedK x <&> GPoly
        GBody x ->
            withDict (recursive :: RecursiveDict ast KNodes) $
            withDict (recursive :: RecursiveDict ast KFunctor) $
            withDict (recursive :: RecursiveDict ast KFoldable) $
            withDict (recursive :: RecursiveDict ast KTraversable) $
            -- KTraversable will be required when not implied by Recursively
            traverseKWith
            (Proxy ::
                Proxy
                '[Recursively KNodes, Recursively KFunctor, Recursively KFoldable, Recursively KTraversable])
            (Lens.from _Flip sequenceC) x
            <&> GBody
        <&> MkFlip

-- | Generalize a unification term pointed by the given variable to a `GTerm`.
-- Unification variables that are scoped within the term
-- become universally quantified skolems.
generalize ::
    forall m t.
    Recursively (Unify m) t =>
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
                withDict (recursive :: RecursiveDict t (Unify m)) $
                do
                    bindVar binding v1 (UResolving t)
                    r <- traverseKWith p generalize (t ^. uBody)
                    r <$ bindVar binding v1 (UTerm t)
                <&>
                \b ->
                if foldMapKWith p (All . Lens.has _GMono) b ^. Lens._Wrapped
                then GMono v1
                else GBody b
            UResolving t -> GMono v1 <$ occursError v1 t
            _ -> pure (GMono v1)
    where
        p = Proxy :: Proxy '[Recursively (Unify m)]

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
            r <- scopeConstraints <&> (<> l) >>= newVar binding . cons & lift
            UInstantiated r & bindVar binding x & lift
            pure r
    UInstantiated v -> pure v
    _ -> error "unexpected state at instantiate's forall"

-- TODO: Better name?
{-# INLINE instantiateH #-}
instantiateH ::
    forall m t.
    Applicative m =>
    Tree (RecursiveNodes t) (KDict '[Unify m]) ->
    Tree (GTerm (UVarOf m)) t -> WriterT [m ()] m (Tree (UVarOf m) t)
instantiateH _ (GMono x) = pure x
instantiateH c (GBody x) =
    withDict (c ^. recSelf . _KDict) $
    traverseKRec c instantiateH x >>= lift . newTerm
instantiateH c (GPoly x) =
    withDict (c ^. recSelf . _KDict) $
    instantiateForAll UUnbound x

{-# INLINE instantiateWith #-}
instantiateWith ::
    forall m t a.
    (Recursively KNodes t, Recursively (Unify m) t) =>
    m a ->
    Tree (GTerm (UVarOf m)) t ->
    m (Tree (UVarOf m) t, a)
instantiateWith action g =
    do
        (r, recover) <-
            instantiateH (rLiftConstraints :: Tree (RecursiveNodes t) (KDict '[Unify m])) g
            & runWriterT
        action <* sequence_ recover <&> (r, )

-- | Instantiate a `Generalized` type with fresh unification variables
-- for the quantified variables
{-# INLINE instantiate #-}
instantiate ::
    (Recursively KNodes t, Recursively (Unify m) t) =>
    Tree (GTerm (UVarOf m)) t -> m (Tree (UVarOf m) t)
instantiate g = instantiateWith (pure ()) g <&> (^. Lens._1)

type Deps c v t = ((c (v t), c (Node t (GTerm v))) :: Constraint)
deriving instance Deps Eq   v t => Eq   (GTerm v t)
deriving instance Deps Ord  v t => Ord  (GTerm v t)
deriving instance Deps Show v t => Show (GTerm v t)
instance Deps Binary v t => Binary (GTerm v t)
instance Deps NFData v t => NFData (GTerm v t)
