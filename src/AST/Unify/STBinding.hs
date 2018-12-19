{-# LANGUAGE NoImplicitPrelude, TypeFamilies, TemplateHaskell #-}

module AST.Unify.STBinding
    ( STVar, stBindingState
    ) where

import           AST.Unify (Binding(..), UniVar)
import           AST.Unify.Term (UTerm(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.ST.Class (MonadST(..))
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import           Prelude.Compat

newtype STVar s t = STVar (STRef s (Maybe (UTerm (STVar s) t)))
Lens.makePrisms ''STVar

instance Eq (STVar s a) where
    STVar x == STVar y = x == y

stBindingState ::
    (MonadST m, UniVar m ~ STVar (World m)) =>
    Binding m t
stBindingState =
    Binding
    { lookupVar = liftST . readSTRef . (^. _STVar)
    , newVar = newSTRef Nothing & liftST <&> STVar
    , bindVar = \v t -> writeSTRef (v ^. _STVar) (Just t) & liftST
    }
