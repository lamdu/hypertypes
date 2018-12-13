{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies #-}

module AST.Unify.IntMapBinding
    ( IntBindingState, emptyIntBindingState
    , intBindingState, intVisit
    ) where

import           AST.Functor.UTerm (UTerm(..))
import           AST.Node (Node)
import           AST.Unify (UniVar, Binding(..))
import           Control.Applicative (Alternative(..))
import qualified Control.Lens as Lens
import           Control.Lens (ALens')
import           Control.Lens.Operators
import           Control.Monad.State (MonadState(..), modify)
import           Data.Functor.Const (Const(..))
import           Data.IntMap (IntMap)
import           Data.IntSet (IntSet)

import           Prelude.Compat

data IntBindingState t = IntBindingState
    { _nextFreeVar :: {-# UNPACK #-} !Int
    , _varBindings :: IntMap (Node (UTerm (Const Int)) t)
    }
Lens.makeLenses ''IntBindingState

emptyIntBindingState :: IntBindingState t
emptyIntBindingState = IntBindingState 0 mempty

increase ::
    MonadState s m =>
    ALens' s Int -> m Int
increase l =
    do
        r <- Lens.use (Lens.cloneLens l)
        r <$ modify (Lens.cloneLens l +~ 1)

intBindingState ::
    (MonadState s m, UniVar m ~ Const Int) =>
    ALens' s (IntBindingState t) ->
    Binding m t
intBindingState l =
    Binding
    { lookupVar = \k -> Lens.use (Lens.cloneLens l . varBindings . Lens.at (k ^. Lens._Wrapped))
    , newVar = increase (Lens.cloneLens l . nextFreeVar) <&> UVar . Const
    , bindVar = \k v -> Lens.cloneLens l . varBindings . Lens.at (k ^. Lens._Wrapped) ?= v
    }

intVisit :: Alternative m => Const Int f -> IntSet -> m IntSet
intVisit (Const var) =
    Lens.contains var x
    where
        x True = empty
        x False = pure True
