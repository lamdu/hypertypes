{-# LANGUAGE NoImplicitPrelude, TypeFamilies #-}

module AST.Unify.STBindingState
    ( STVar
    , stBindingState
    ) where

import           AST.Unify (Binding(..), UTerm(..), Var)
import           Control.Lens.Operators
import           Control.Monad.ST (ST)
import           Control.Monad.ST.Class (MonadST(..))
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import           Prelude.Compat

data STVar s a =
    STVar
    { -- For occurs check.
      -- A (more efficient?) alternative would mark the state in the referenced value itself!
      _varId :: Int
    , varRef :: STRef s (Maybe (UTerm (STVar s) a))
    }

newtype STBindingState s (t :: (* -> *) -> *) = STBState (STRef s Int)

type instance Var (ST s) = STVar s

stBindingState ::
    (MonadST m, Var m ~ STVar (World m)) =>
    m (STBindingState (World m) t) ->
    Binding m t
stBindingState getState =
    Binding
    { lookupVar = liftST . readSTRef . varRef
    , newVar =
        do
            STBState nextFreeVarRef <- getState
            do
                nextFreeVar <- readSTRef nextFreeVarRef
                writeSTRef nextFreeVarRef (nextFreeVar + 1)
                newSTRef Nothing <&> STVar nextFreeVar
                & liftST
        <&> UVar
    , bindVar =
        \v t -> writeSTRef (varRef v) (Just t) & liftST
    }
