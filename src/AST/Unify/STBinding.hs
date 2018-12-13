{-# LANGUAGE NoImplicitPrelude, TypeFamilies, TemplateHaskell #-}

module AST.Unify.STBinding
    ( STVar, stBindingState
    ) where

import           AST.Functor.UTerm (UTerm(..))
import           AST.Unify (Binding(..), UniVar)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.ST.Class (MonadST(..))
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import           Prelude.Compat

newtype STVar s a = STVar (STRef s (Maybe (UTerm (STVar s) a)))
Lens.makePrisms ''STVar

instance Eq (STVar s a) where
    STVar x == STVar y = x == y

stBindingState ::
    (MonadST m, UniVar m ~ STVar (World m)) =>
    Binding m t
stBindingState =
    Binding
    { lookupVar = liftST . readSTRef . (^. _STVar)
    , newVar = newSTRef Nothing & liftST <&> UVar . STVar
    , bindVar =
        \v t -> writeSTRef (v ^. _STVar) (Just t) & liftST
    }
