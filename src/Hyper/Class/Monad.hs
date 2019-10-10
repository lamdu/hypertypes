-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.HyperType's

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.Monad
    ( HMonad(..), hbind
    ) where

import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import Hyper.Class.Apply (HApplicative)
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HWitness, (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Combinator.Compose (HCompose, _HCompose)
import Hyper.Type (Tree)
import Hyper.Type.Pure (Pure(..), _Pure)

import Prelude.Compat

-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.HyperType's
class HApplicative h => HMonad h where
    hjoin ::
        Recursively HFunctor p =>
        Tree (HCompose h h) p ->
        Tree h p

instance HMonad Pure where
    hjoin x =
        withDict (recursively (p x)) $
        _Pure #
        hmap (Proxy @(Recursively HFunctor) #> hjoin)
        (x ^. _HCompose . _Pure . _HCompose . _Pure . _HCompose)
        where
            p :: Tree (HCompose Pure Pure) p -> Proxy (HFunctor p)
            p _ = Proxy

-- | A variant of 'Control.Monad.(>>=)' for 'Hyper.Type.HyperType's
hbind ::
    (HMonad h, Recursively HFunctor p) =>
    Tree h p ->
    (forall n. HWitness h n -> Tree p n -> Tree (HCompose h p) n) ->
    Tree h p
hbind x f = _HCompose # hmap f x & hjoin
