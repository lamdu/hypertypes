-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.AHyperType's

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.Monad
    ( KMonad(..), bindK
    ) where

import Hyper.Class.Apply (KApplicative)
import Hyper.Class.Functor (KFunctor(..))
import Hyper.Class.Nodes (KNodes(..), (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Combinator.Compose (Compose, _Compose)
import Hyper.Type (Tree)
import Hyper.Type.Pure (Pure(..), _Pure)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.AHyperType's
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

-- | A variant of 'Control.Monad.(>>=)' for 'Hyper.Type.AHyperType's
bindK ::
    (KMonad k, Recursively KFunctor p) =>
    Tree k p ->
    (forall n. KWitness k n -> Tree p n -> Tree (Compose k p) n) ->
    Tree k p
bindK x f = _Compose # mapK f x & joinK
