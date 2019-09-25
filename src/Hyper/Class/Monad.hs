-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.AHyperType's

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.Monad
    ( HMonad(..), bindK
    ) where

import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import Hyper.Class.Apply (HApplicative)
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..), (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Type (Tree)
import Hyper.Type.Combinator.Compose (Compose, _Compose)
import Hyper.Type.Pure (Pure(..), _Pure)

import Prelude.Compat

-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.AHyperType's
class HApplicative k => HMonad k where
    joinK ::
        Recursively HFunctor p =>
        Tree (Compose k k) p ->
        Tree k p

instance HMonad Pure where
    joinK x =
        withDict (recursively (p x)) $
        _Pure #
        mapK (Proxy @(Recursively HFunctor) #> joinK)
        (x ^. _Compose . _Pure . _Compose . _Pure . _Compose)
        where
            p :: Tree (Compose Pure Pure) p -> Proxy (HFunctor p)
            p _ = Proxy

-- | A variant of 'Control.Monad.(>>=)' for 'Hyper.Type.AHyperType's
bindK ::
    (HMonad k, Recursively HFunctor p) =>
    Tree k p ->
    (forall n. HWitness k n -> Tree p n -> Tree (Compose k p) n) ->
    Tree k p
bindK x f = _Compose # mapK f x & joinK
