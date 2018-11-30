{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies #-}

module AST.Unify.IntMapBinding
    ( IntBindingState, emptyIntBindingState
    , intBindingState, intVisit
    ) where

import           AST (Node)
import           AST.Unify (UTerm(..), Var, Binding(..))
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

intBindingState ::
    (MonadState s m, Var m ~ Const Int) =>
    ALens' s (IntBindingState t) ->
    Binding m t
intBindingState l =
    Binding
    { lookupVar = \k -> Lens.use (Lens.cloneLens l . varBindings . Lens.at (k ^. Lens._Wrapped))
    , newVar =
        do
            r <- Lens.use (Lens.cloneLens l . nextFreeVar)
            UVar (Const r) <$ modify (Lens.cloneLens l . nextFreeVar +~ 1)
    , bindVar = \k v -> Lens.cloneLens l . varBindings . Lens.at (k ^. Lens._Wrapped) ?= v
    }

intVisit :: Const Int f -> IntSet -> Maybe IntSet
intVisit (Const var) =
    Lens.contains var x
    where
        x True = Nothing
        x False = pure True
