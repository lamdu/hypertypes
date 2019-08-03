{-# LANGUAGE FlexibleContexts, RankNTypes #-}

module AST.Class.Monad
    ( KMonad(..)
    , bindK, bindKWith
    ) where

import AST.Class
import AST.Class.Combinators
import AST.Class.Recursive (Recursively(..), RecursiveDict)
import AST.Combinator.Compose (Compose, _Compose)
import AST.Knot (Tree)
import AST.Knot.Pure (Pure(..), _Pure)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Constraint.List (ApplyConstraints)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class KApplicative k => KMonad k where
    joinK ::
        Recursively KFunctor l =>
        Tree (Compose k k) l ->
        Tree k l

instance KMonad Pure where
    joinK x =
        withDict (r x) $
        x ^. _Compose . _Pure . _Compose . _Pure . _Compose
        & mapKWith (Proxy @'[Recursively KFunctor]) joinK
        & MkPure
        where
            r :: Recursively KFunctor l => Tree k l -> RecursiveDict l KFunctor
            r _ = recursive

bindK ::
    (KMonad k, Recursively KFunctor l) =>
    Tree k l ->
    (forall c. Tree l c -> Tree (Compose k l) c) ->
    Tree k l
bindK x f = _Compose # mapK f x & joinK

bindKWith ::
    (KMonad k, Recursively KFunctor l, KLiftConstraints k constraints) =>
    Proxy constraints ->
    Tree k l ->
    (forall c. ApplyConstraints constraints c => Tree l c -> Tree (Compose k l) c) ->
    Tree k l
bindKWith p x f =
    _Compose # mapKWith p f x & joinK
