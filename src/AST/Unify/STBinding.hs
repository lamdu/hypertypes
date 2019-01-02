{-# LANGUAGE NoImplicitPrelude, TypeFamilies, TemplateHaskell, DataKinds #-}

module AST.Unify.STBinding
    ( STVar(..), _STVar
    , stBindingState
    , newStQuantified
    ) where

import           AST.Knot (Knot)
import           AST.Unify (Binding(..), UVar)
import           AST.Unify.Term (UTerm(..))
import           Control.Lens (ALens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader.Class (MonadReader(..))
import           Control.Monad.ST.Class (MonadST(..))
import           Data.Functor.Const (Const(..))
import           Data.STRef (STRef, newSTRef, readSTRef, writeSTRef)

import           Prelude.Compat

newtype STVar s t = STVar (STRef s (UTerm (STVar s) t))
Lens.makePrisms ''STVar

instance Eq (STVar s a) where
    STVar x == STVar y = x == y

stBindingState ::
    (MonadST m, UVar m ~ STVar (World m)) =>
    Binding m t
stBindingState =
    Binding
    { lookupVar = liftST . readSTRef . (^. _STVar)
    , newVar = \t -> newSTRef t & liftST <&> STVar
    , bindVar = \v t -> writeSTRef (v ^. _STVar) t & liftST
    }

readModifySTRef :: MonadST m => STRef (World m) a -> (a -> a) -> m (a, a)
readModifySTRef ref func =
    do
        old <- readSTRef ref & liftST
        let new = func old
        (old, new) <$ (new `seq` liftST (writeSTRef ref new))

newStQuantified ::
    (MonadReader env m, MonadST m, Enum a) =>
    ALens' env (Const (STRef (World m) a) (ast :: Knot)) ->
    m a
newStQuantified l =
    Lens.view (Lens.cloneLens l . Lens._Wrapped)
    >>= fmap fst . (`readModifySTRef` succ)
