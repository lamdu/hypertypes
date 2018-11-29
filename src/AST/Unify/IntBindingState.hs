{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, FlexibleContexts, TypeFamilies #-}

module AST.Unify.IntBindingState
    ( IntBindingState(..), nextFreeVar, varBindings
    , emptyIntBindingState
    , intBindingState
    , visitSet
    ) where

import           AST (Node)
import           AST.Unify
import qualified Control.Lens as Lens
import           Control.Lens (ALens')
import           Control.Lens.Operators
import           Control.Monad.Except (MonadError(..))
import           Control.Monad.State (MonadState(..), modify)
import           Data.IntMap (IntMap)
import           Data.IntSet (IntSet)

import           Prelude.Compat

data IntBindingState m t = IntBindingState
    { _nextFreeVar :: {-# UNPACK #-} !Int
    , _varBindings :: IntMap (Node (UTerm (Var m)) t)
    }
Lens.makeLenses ''IntBindingState

emptyIntBindingState :: IntBindingState f t
emptyIntBindingState = IntBindingState 0 mempty

intBindingState ::
    ( Var m (Node (UTerm (Var m)) t) ~ Int
    , MonadState s m
    ) =>
    ALens' s (IntBindingState m t) -> Binding m t
intBindingState l =
    Binding
    { lookupVar = \k -> Lens.use (Lens.cloneLens l . varBindings . Lens.at k)
    , newVar =
        do
            r <- Lens.use (Lens.cloneLens l . nextFreeVar)
            UVar r <$ modify (Lens.cloneLens l . nextFreeVar +~ 1)
    , bindVar = \k v -> Lens.cloneLens l . varBindings . Lens.at k ?= v
    }

visitSet :: MonadError () m => Int -> IntSet -> m IntSet
visitSet var =
    Lens.contains var x
    where
        x True = throwError ()
        x False = pure True
