{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, LambdaCase #-}

module AST.Unify.Generalize
    ( GTerm, generalize
    ) where

import           Algebra.PartialOrd (PartialOrd(..))
import           AST.Class.Children
import           AST.Class.Instantiate
import           AST.Class.Recursive
import           AST.Knot
import           AST.Unify
import           AST.Unify.Term
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Writer
import           Data.Constraint
import           Data.Monoid (All(..))
import           Data.Proxy

import           Prelude.Compat

data GTerm m ast
    = GMono (UVar m ast)
    | GPoly (UVar m ast)
    | GBody (Tie ast (GTerm m))
Lens.makePrisms ''GTerm

generalize ::
    forall m t.
    Recursive (Unify m) t =>
    Tree (UVar m) t -> m (Tree (GTerm m) t)
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
                children p generalize (t ^. uBody)
                <&> onBody
                where
                    onBody b
                        | foldMapChildren p (All . Lens.has _GMono) b ^. Lens._Wrapped = GMono v1
                        | otherwise = GBody b
            _ -> pure (GMono v1)
    where
        p = Proxy :: Proxy (Recursive (Unify m))

type instance SchemeType (Tree (GTerm v) t) = t

instance Recursive (Unify m) t => Instantiate m (Tree (GTerm m) t) where
    instantiate g =
        do
            (r, recover) <- runWriterT (go g)
            r <$ sequence_ recover
        where
            go ::
                forall child.
                Recursive (Unify m) child =>
                Tree (GTerm m) child -> WriterT [m ()] m (Tree (UVar m) child)
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
