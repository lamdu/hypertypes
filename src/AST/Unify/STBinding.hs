{-# LANGUAGE NoImplicitPrelude, TypeFamilies, FlexibleContexts #-}

module AST.Unify.STBinding
    ( STVar
    , STBindingState, newSTBindingState
    , stBindingState, stVisit
    , stBindingToInt
    ) where

import           AST (Node)
import           AST.Recursive (Recursive(..), hoistNodeR)
import           AST.Unify (Binding(..), UTerm(..), Var, _UVar)
import           Control.Applicative (Alternative(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.ST.Class (MonadST(..))
import           Data.Functor.Const (Const(..))
import           Data.IntSet (IntSet)
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import           Prelude.Compat

data STVar s a =
    STVar
    { -- For occurs check.
      -- A (more efficient?) alternative would mark the state in the referenced value itself!
      varId :: Int
    , varRef :: STRef s (Maybe (UTerm (STVar s) a))
    }

instance Eq (STVar s a) where
    STVar x _ == STVar y _ = x == y

newtype STBindingState s (t :: (* -> *) -> *) = STBState (STRef s Int)

newSTBindingState :: MonadST m => m (STBindingState (World m) t)
newSTBindingState = newSTRef 0 & liftST <&> STBState

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

stVisit :: Alternative f => STVar s a -> IntSet -> f IntSet
stVisit (STVar idx _) =
    Lens.contains idx x
    where
        x True = empty
        x False = pure True

stBindingToInt ::
    Recursive t =>
    Node (UTerm (STVar s)) t -> Node (UTerm (Const Int)) t
stBindingToInt = hoistNodeR (_UVar %~ Const . varId)
