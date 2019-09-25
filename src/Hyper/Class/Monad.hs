-- | A variant of 'Control.Monad.Monad' for 'Hyper.Type.HyperType's

{-# LANGUAGE FlexibleContexts #-}

module Hyper.Class.Monad
    ( HMonad(..), bindH
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
    joinH ::
        Recursively HFunctor p =>
        Tree (Compose h h) p ->
        Tree h p

instance HMonad Pure where
    joinH x =
        withDict (recursively (p x)) $
        _Pure #
        mapH (Proxy @(Recursively HFunctor) #> joinH)
        (x ^. _Compose . _Pure . _Compose . _Pure . _Compose)
        where
            p :: Tree (Compose Pure Pure) p -> Proxy (HFunctor p)
            p _ = Proxy

-- | A variant of 'Control.Monad.(>>=)' for 'Hyper.Type.HyperType's
bindH ::
    (HMonad h, Recursively HFunctor p) =>
    Tree h p ->
    (forall n. HWitness h n -> Tree p n -> Tree (Compose h p) n) ->
    Tree h p
bindH x f = _Compose # mapH f x & joinH
