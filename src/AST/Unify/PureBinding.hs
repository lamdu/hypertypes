{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, DataKinds #-}

module AST.Unify.PureBinding
    ( PureBinding, emptyPureBinding
    , pureBinding
    , increase
    ) where

import           AST.Knot (Tree)
import           AST.Unify (UVar, Binding(..))
import           AST.Unify.Term
import qualified Control.Lens as Lens
import           Control.Lens (ALens')
import           Control.Lens.Operators
import           Control.Monad.State (MonadState(..), modify)
import           Data.Functor.Const (Const(..))
import           Data.Sequence
import qualified Data.Sequence as Sequence

import           Prelude.Compat

newtype PureBinding t = PureBinding (Seq (UTerm (Const Int) t))
Lens.makePrisms ''PureBinding

emptyPureBinding :: PureBinding t
emptyPureBinding = PureBinding mempty

increase ::
    MonadState s m =>
    ALens' s Int -> m Int
increase l =
    do
        r <- Lens.use (Lens.cloneLens l)
        r <$ modify (Lens.cloneLens l +~ 1)

pureBinding ::
    (MonadState s m, UVar m ~ Const Int) =>
    ALens' s (Tree PureBinding t) ->
    Binding m t
pureBinding l =
    Binding
    { lookupVar =
        \k ->
        Lens.use (Lens.cloneLens l . _PureBinding)
        <&> (`Sequence.index` (k ^. Lens._Wrapped))
    , newVar =
        \x ->
        do
            s <- Lens.use (Lens.cloneLens l . _PureBinding)
            Const (Sequence.length s) <$ (Lens.cloneLens l . _PureBinding .= s Sequence.|> x)
    , bindVar = bind
    }
    where
        bind k v = Lens.cloneLens l . _PureBinding %= Sequence.update (k ^. Lens._Wrapped) v
