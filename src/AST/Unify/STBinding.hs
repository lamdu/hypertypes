{-# LANGUAGE NoImplicitPrelude, TypeFamilies, FlexibleContexts, TemplateHaskell #-}

module AST.Unify.STBinding
    ( STVar
    , STBindingState, newSTBindingState
    , stBindingState, stVisit
    , stBindingToInt
    ) where

import           AST.Class.Children (Children)
import           AST.Class.Recursive (Recursive, hoistNodeR)
import           AST.Functor.UTerm
import           AST.Node (Node)
import           AST.Unify (Binding(..), Var)
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

data STBindingState s (t :: (* -> *) -> *) =
    STBState
    { _nextFreeVar :: STRef s Int
    , _nextTerm :: STRef s Int
    }
Lens.makeLenses ''STBindingState

newSTBindingState :: MonadST m => m (STBindingState (World m) t)
newSTBindingState =
    STBState
    <$> newSTRef 0
    <*> newSTRef 0
    & liftST

increase :: MonadST m => STRef (World m) Int -> m Int
increase v =
    do
        r <- readSTRef v
        r <$ writeSTRef v (r + 1)
    & liftST

stBindingState ::
    (MonadST m, Var m ~ STVar (World m)) =>
    m (STBindingState (World m) t) ->
    Binding m t
stBindingState getState =
    Binding
    { lookupVar = liftST . readSTRef . varRef
    , newVar =
        STVar
        <$> (getState <&> (^. nextFreeVar) >>= increase)
        <*> liftST (newSTRef Nothing)
        <&> UVar
    , newTerm =
        \t ->
        getState <&> (^. nextTerm) >>= increase
        <&> (`UBody` t) <&> UTerm
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
    Recursive Children t =>
    Node (UTerm (STVar s)) t -> Node (UTerm (Const Int)) t
stBindingToInt = hoistNodeR (_UVar %~ Const . varId)
