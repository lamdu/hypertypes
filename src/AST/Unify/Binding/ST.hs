{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Unify.Binding.ST
    ( STVar(..), _STVar
    , stBinding
    ) where

import           AST.Class.Unify (BindingDict(..))
import           AST.Unify.Term (UTerm(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.ST.Class (MonadST(..))
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import           Prelude.Compat

newtype STVar s t = STVar (STRef s (UTerm (STVar s) t))
    deriving Eq
Lens.makePrisms ''STVar

{-# INLINE stBinding #-}
stBinding ::
    MonadST m =>
    BindingDict (STVar (World m)) m t
stBinding =
    BindingDict
    { lookupVar = liftST . readSTRef . (^. _STVar)
    , newVar = \t -> newSTRef t & liftST <&> STVar
    , bindVar = \v t -> writeSTRef (v ^. _STVar) t & liftST
    }
