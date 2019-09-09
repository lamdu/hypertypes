{-# LANGUAGE RankNTypes, FlexibleContexts #-}

module AST.Class.Monad
    ( KMonad(..), bindK
    ) where

import AST.Class.Apply (KApplicative)
import AST.Class.Functor (KFunctor(..))
import AST.Class.Nodes (KNodes(..), (#>))
import AST.Class.Recursive (Recursively(..))
import AST.Combinator.Compose (Compose, _Compose)
import AST.Knot (Tree)
import AST.Knot.Pure (Pure(..), _Pure)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

import Prelude.Compat

class KApplicative k => KMonad k where
    joinK ::
        Recursively KFunctor p =>
        Tree (Compose k k) p ->
        Tree k p

instance KMonad Pure where
    joinK x =
        withDict (recursively (p x)) $
        _Pure #
        mapK (Proxy @(Recursively KFunctor) #> joinK)
        (x ^. _Compose . _Pure . _Compose . _Pure . _Compose)
        where
            p :: Tree (Compose Pure Pure) p -> Proxy (KFunctor p)
            p _ = Proxy

bindK ::
    (KMonad k, Recursively KFunctor p) =>
    Tree k p ->
    (forall n. KWitness k n -> Tree p n -> Tree (Compose k p) n) ->
    Tree k p
bindK x f = _Compose # mapK f x & joinK
