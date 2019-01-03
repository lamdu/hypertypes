{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, LambdaCase, InstanceSigs, RankNTypes #-}

module AST.Unify.Generalize
    ( Generalized(..), _Generalized
    , generalize, monomorphic
    , -- TODO: should these not be exported? (Internals)
      GTerm(..), _GMono, _GPoly, _GBody
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import           AST.Class.Children (Children(..), foldMapChildren)
import           AST.Class.Children.TH (makeChildren)
import           AST.Class.Instantiate (Instantiate(..), SchemeType)
import           AST.Class.Recursive (Recursive(..), RecursiveDict)
import           AST.Knot (RunKnot, Tree, Tie)
import           AST.Unify
import           AST.Unify.Term (UTerm(..), uBody)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Writer (WriterT(..), tell)
import           Data.Constraint (withDict)
import           Data.Monoid (All(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

data GTerm v ast
    = GMono (v ast)
    | GPoly (v ast)
    | GBody (Tie ast (GTerm v))
Lens.makePrisms ''GTerm
makeChildren ''GTerm

newtype Generalized ast v = Generalized (Tree (GTerm (RunKnot v)) ast)
Lens.makePrisms ''Generalized

instance Children ast => Children (Generalized ast) where
    type ChildrenConstraint (Generalized ast) cls = Recursive cls ast
    children ::
        forall f constraint n m.
        (Applicative f, Recursive constraint ast) =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child -> f (Tree m child)) ->
        Tree (Generalized ast) n -> f (Tree (Generalized ast) m)
    children p f (Generalized g) =
        withDict (recursive :: RecursiveDict constraint ast) $
        case g of
        GMono x -> f x <&> GMono
        GPoly x -> f x <&> GPoly
        GBody x ->
            children (Proxy :: Proxy (Recursive constraint))
            (fmap (^. _Generalized) . children p f . Generalized) x
            <&> GBody
        <&> Generalized

type instance SchemeType (Tree (Generalized t) v) = t

instance (v ~ UVar m, Recursive (Unify m) t) => Instantiate m (Tree (Generalized t) v) where
    instantiate (Generalized g) =
        do
            (r, recover) <- runWriterT (go g)
            r <$ sequence_ recover
        where
            go ::
                forall child.
                Recursive (Unify m) child =>
                Tree (GTerm (UVar m)) child -> WriterT [m ()] m (Tree (UVar m) child)
            go =
                withDict (recursive :: RecursiveDict (Unify m) child) $
                \case
                GMono x -> pure x
                GBody x -> children (Proxy :: Proxy (Recursive (Unify m))) go x >>= lift . newTerm
                GPoly x ->
                    lookupVar binding x & lift
                    >>=
                    \case
                    USkolem l ->
                        do
                            tell [bindVar binding x (USkolem l)]
                            r <- lift newUnbound
                            UVar r & bindVar binding x & lift
                            pure r
                    UVar v -> pure v
                    _ -> error "unexpected state at instantiate's forall"

generalize ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UVar m) t -> m (Tree (Generalized t) (UVar m))
generalize v0 =
    withDict (recursive :: RecursiveDict (Unify m) t) $
    do
        (v1, u) <- semiPruneLookup v0
        c <- scopeConstraints (Proxy :: Proxy t)
        case u of
            UUnbound l | l `leq` c ->
                GPoly v1 <$
                -- We set the variable to a skolem,
                -- so additional unifications after generalization
                -- (for example hole resumptions where supported)
                -- cannot unify it with anything.
                bindVar binding v1 (USkolem l)
            USkolem l | l `leq` c -> pure (GPoly v1)
            UTerm t ->
                children p (fmap (^. _Generalized) . generalize) (t ^. uBody)
                <&> onBody
                where
                    onBody b
                        | foldMapChildren p (All . Lens.has _GMono) b ^. Lens._Wrapped = GMono v1
                        | otherwise = GBody b
            _ -> pure (GMono v1)
    <&> Generalized
    where
        p = Proxy :: Proxy (Recursive (Unify m))

monomorphic :: Tree v t -> Tree (Generalized t) v
monomorphic = Generalized . GMono
