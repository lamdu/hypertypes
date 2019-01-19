{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Unify.Binding.ST
    ( STVar(..), _STVar
    , stBinding
    ) where

import           AST.Unify.Binding (Binding(..))
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
    Binding (STVar (World m)) m t
stBinding =
    Binding
    { lookupVar = liftST . readSTRef . (^. _STVar)
    , newVar = \t -> newSTRef t & liftST <&> STVar
    , bindVar = \v t -> writeSTRef (v ^. _STVar) t & liftST
    }
