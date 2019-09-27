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
import Hyper.Class.Nodes (HNodes(..), (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Type (Tree)
import Hyper.Type.Combinator.Compose (Compose, _Compose)
import Hyper.Type.Pure (Pure(..), _Pure)

import Prelude.Compat

-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.HyperType's
class HApplicative h => HMonad h where
    hjoin ::
        Recursively HFunctor p =>
        Tree (Compose h h) p ->
        Tree h p

instance HMonad Pure where
    hjoin x =
        withDict (recursively (p x)) $
        _Pure #
        hmap (Proxy @(Recursively HFunctor) #> hjoin)
        (x ^. _Compose . _Pure . _Compose . _Pure . _Compose)
        where
            p :: Tree (Compose Pure Pure) p -> Proxy (HFunctor p)
            p _ = Proxy

-- | A variant of 'Control.Monad.(>>=)' for 'Hyper.Type.HyperType's
hbind ::
    (HMonad h, Recursively HFunctor p) =>
    Tree h p ->
    (forall n. HWitness h n -> Tree p n -> Tree (Compose h p) n) ->
    Tree h p
hbind x f = _Compose # hmap f x & hjoin
