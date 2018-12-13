{-# LANGUAGE NoImplicitPrelude, TypeFamilies #-}

module AST.Unify.STBinding
    ( STVar
    , STBindingState, newSTBindingState
    , stBindingState
    ) where

import           AST.Functor.UTerm (UTerm(..))
import           AST.Unify (Binding(..), UniVar)
import           Control.Lens.Operators
import           Control.Monad.ST.Class (MonadST(..))
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import           Prelude.Compat

data STVar s a =
    STVar
    { -- For comparison
      _varId :: Int
    , varRef :: STRef s (Maybe (UTerm (STVar s) a))
    }

instance Eq (STVar s a) where
    STVar x _ == STVar y _ = x == y

newtype STBindingState s (t :: (* -> *) -> *) = STBState (STRef s Int)

newSTBindingState :: MonadST m => m (STBindingState (World m) t)
newSTBindingState = newSTRef 0 & liftST <&> STBState

increase :: MonadST m => STRef (World m) Int -> m Int
increase v =
    do
        r <- readSTRef v
        r <$ writeSTRef v (r + 1)
    & liftST

stBindingState ::
    (MonadST m, UniVar m ~ STVar (World m)) =>
    m (STBindingState (World m) t) ->
    Binding m t
stBindingState getState =
    Binding
    { lookupVar = liftST . readSTRef . varRef
    , newVar =
        do
            STBState nextFreeVarRef <- getState
            STVar <$> increase nextFreeVarRef <*> newSTRef Nothing
                & liftST
        <&> UVar
    , bindVar =
        \v t -> writeSTRef (varRef v) (Just t) & liftST
    }
