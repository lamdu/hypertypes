{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, DataKinds #-}

module AST.Unify.Binding.Pure
    ( PureBinding(..), _PureBinding
    , emptyPureBinding
    , pureBinding
    ) where

import           AST.Knot (Tree)
import           AST.Unify.Binding (Binding(..))
import           AST.Unify.Term
import qualified Control.Lens as Lens
import           Control.Lens (ALens')
import           Control.Lens.Operators
import           Control.Monad.State (MonadState(..))
import           Data.Functor.Const (Const(..))
import           Data.Sequence
import qualified Data.Sequence as Sequence

import           Prelude.Compat

newtype PureBinding t = PureBinding (Seq (UTerm (Const Int) t))
Lens.makePrisms ''PureBinding

emptyPureBinding :: PureBinding t
emptyPureBinding = PureBinding mempty

{-# INLINE pureBinding #-}
pureBinding ::
    MonadState s m =>
    ALens' s (Tree PureBinding t) ->
    Binding (Const Int) m t
pureBinding l =
    Binding
    { lookupVar =
        \k ->
        Lens.use (Lens.cloneLens l . _PureBinding)
        <&> (^?! Lens.ix (k ^. Lens._Wrapped))
    , newVar =
        \x ->
        Lens.cloneLens l . _PureBinding <<%= (Sequence.|> x)
        <&> Sequence.length <&> Const
    , bindVar =
        \k v ->
        Lens.cloneLens l . _PureBinding . Lens.ix (k ^. Lens._Wrapped) .= v
    }
