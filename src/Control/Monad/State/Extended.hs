{-# LANGUAGE NoImplicitPrelude #-}

module Control.Monad.State.Extended
    ( module Control.Monad.State
    , localState
    ) where

import           Control.Monad.State

import           Prelude.Compat

-- | Run a state action and undo the state changes at the end.
-- Note: Borrowed from `unification-fd`
{-# INLINE localState #-}
localState :: MonadState s m => m a -> m a
localState act =
    do
        saved <- get
        act <* put saved
