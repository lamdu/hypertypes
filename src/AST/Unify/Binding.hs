{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, DataKinds #-}
{-# LANGUAGE StandaloneDeriving, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module AST.Unify.Binding
    ( Binding(..), _Binding
    , emptyBinding
    , bindingDict
    ) where

import           AST.Class.Unify (BindingDict(..))
import           AST.Knot (Tree)
import           AST.Unify.Term
import           Control.Lens (ALens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.State (MonadState(..))
import           Data.Functor.Const (Const(..))
import           Data.Sequence
import qualified Data.Sequence as Sequence

import           Prelude.Compat

newtype Binding t = Binding (Seq (UTerm (Const Int) t))
Lens.makePrisms ''Binding

emptyBinding :: Binding t
emptyBinding = Binding mempty

{-# INLINE bindingDict #-}
bindingDict ::
    MonadState s m =>
    ALens' s (Tree Binding t) ->
    BindingDict (Const Int) m t
bindingDict l =
    BindingDict
    { lookupVar =
        \k ->
        Lens.use (Lens.cloneLens l . _Binding)
        <&> (^?! Lens.ix (k ^. Lens._Wrapped))
    , newVar =
        \x ->
        Lens.cloneLens l . _Binding <<%= (Sequence.|> x)
        <&> Sequence.length <&> Const
    , bindVar =
        \k v ->
        Lens.cloneLens l . _Binding . Lens.ix (k ^. Lens._Wrapped) .= v
    }

deriving instance UTermDeps Eq   (Const Int) t => Eq   (Binding t)
deriving instance UTermDeps Ord  (Const Int) t => Ord  (Binding t)
deriving instance UTermDeps Show (Const Int) t => Show (Binding t)
