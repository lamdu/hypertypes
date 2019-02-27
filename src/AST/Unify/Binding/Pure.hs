{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, DataKinds #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module AST.Unify.Binding.Pure
    ( PureBinding(..), _PureBinding
    , emptyPureBinding
    , pureBinding
    ) where

import           AST.Knot (Tree)
import           AST.Unify.Binding (Binding(..))
import           AST.Unify.Term
import           Control.Lens (ALens')
import qualified Control.Lens as Lens
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

deriving instance UTermDeps Eq (Const Int) t => Eq (PureBinding t)
deriving instance UTermDeps Ord (Const Int) t => Ord (PureBinding t)
deriving instance UTermDeps Show (Const Int) t => Show (PureBinding t)
