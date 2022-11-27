-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.HyperType's

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.Monad
    ( HMonad(..), hbind
    ) where

import Hyper.Class.Apply (HApplicative)
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HWitness, (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Combinator.Compose (HCompose, _HCompose)
import Hyper.Type (type (#))
import Hyper.Type.Pure (Pure(..), _Pure)

import Hyper.Internal.Prelude

-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.HyperType's
class HApplicative h => HMonad h where
    hjoin ::
        Recursively HFunctor p =>
        HCompose h h # p ->
        h # p

instance HMonad Pure where
    hjoin x =
        _Pure #
        hmap (Proxy @(Recursively HFunctor) #> hjoin)
        (x ^. _HCompose . _Pure . _HCompose . _Pure . _HCompose)
        \\ recursively (p x)
        where
            p :: HCompose Pure Pure # p -> Proxy (HFunctor p)
            p _ = Proxy

-- | A variant of 'Control.Monad.(>>=)' for 'Hyper.Type.HyperType's
hbind ::
    (HMonad h, Recursively HFunctor p) =>
    h # p ->
    (forall n. HWitness h n -> p # n -> HCompose h p # n) ->
    h # p
hbind x f = _HCompose # hmap f x & hjoin
