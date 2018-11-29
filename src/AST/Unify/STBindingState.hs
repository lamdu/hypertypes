{-# LANGUAGE NoImplicitPrelude, KindSignatures #-}

module AST.Unify.STBindingState
    ( STVar
    , stBindingState
    ) where

import           AST (Node)
import           AST.Unify (Binding(..), UTerm(..))
import           Control.Lens.Operators
import           Control.Monad.ST (ST)
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Reader (ReaderT, asks)
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import           Prelude.Compat

data STVar s t =
    STVar
    { -- For occurs check.
      -- A (more efficient?) alternative would mark the state in the referenced value itself!
      _varId :: Int
    , varRef :: STRef s (Maybe (Node (UTerm (STVar s t)) t))
    }

newtype STBindingState s (t :: (* -> *) -> *) = STBState (STRef s Int)

stBindingState ::
    (env -> STBindingState s t) ->
    Binding (STVar s t) t (ReaderT env (ST s))
stBindingState l =
    Binding
    { lookupVar = lift . readSTRef . varRef
    , newVar =
        do
            STBState nextFreeVarRef <- asks l
            do
                nextFreeVar <- readSTRef nextFreeVarRef
                writeSTRef nextFreeVarRef (nextFreeVar + 1)
                newSTRef Nothing <&> STVar nextFreeVar
                & lift
        <&> UVar
    , bindVar = \v t -> writeSTRef (varRef v) (Just t) & lift
    }
