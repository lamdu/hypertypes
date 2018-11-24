{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, FlexibleContexts #-}

module AST.Unify.IntBindingState
    ( IntBindingState(..), nextFreeVar, varBindings
    , intBindingState
    ) where

import           AST
import           AST.Unify
import qualified Control.Lens as Lens
import           Control.Lens (ALens')
import           Control.Lens.Operators
import           Control.Monad
import           Control.Monad.Except (MonadError(..))
import           Control.Monad.State
import           Data.Functor.Identity (Identity(..))
import           Data.IntMap (IntMap)
import           Data.Maybe (fromMaybe)
import           Data.Proxy

import           Prelude.Compat

data IntBindingState t = IntBindingState
    { _nextFreeVar :: {-# UNPACK #-} !Int
    , _varBindings :: IntMap (t (UTerm Int))
    }
Lens.makeLenses ''IntBindingState

intBindingState :: MonadState s m => ALens' s (IntBindingState t) -> Binding Int t m
intBindingState l =
    Binding
    { lookupVar = \k -> Lens.use (Lens.cloneLens l . varBindings . Lens.at k) <&> fromMaybe (error "var not found")
    , newVar =
        do
            r <- Lens.use (Lens.cloneLens l . nextFreeVar)
            UVar r <$ modify (Lens.cloneLens l . nextFreeVar +~ 1)
    , bindVar = \k v -> Lens.cloneLens l . varBindings . Lens.at k ?= v
    }
