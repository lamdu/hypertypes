{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}

module AST.Unify.IntBindingState
    ( IntBindingState(..), nextFreeVar, varBindings
    ) where

import           AST
import           AST.Unify
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad
import           Control.Monad.Except (MonadError(..))
import           Control.Monad.Trans.State
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

instance Monad m => BindingMonad t (StateT (IntBindingState t) m) where
    type Var t (StateT (IntBindingState t) m) = Int
    lookupVar k = Lens.use (varBindings . Lens.at k) <&> fromMaybe (error "var not found")
    newVar = Lens.zoom nextFreeVar (state (\x -> (UVar x, x+1)))
    bindVar k v = varBindings . Lens.at k ?= v
