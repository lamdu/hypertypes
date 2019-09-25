-- | A pure data structures implementation of unification variables state

{-# LANGUAGE UndecidableInstances, TemplateHaskell, GeneralizedNewtypeDeriving #-}

module Hyper.Unify.Binding
    ( UVar(..), _UVar
    , Binding(..), _Binding
    , emptyBinding
    , bindingDict
    ) where

import           Control.Lens (ALens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.State (MonadState(..))
import           Data.Sequence
import qualified Data.Sequence as Sequence
import           GHC.Generics (Generic)
import           Hyper.Class.Unify (BindingDict(..))
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Type (Tree, AHyperType)
import           Hyper.Unify.Term

import           Prelude.Compat

-- | A unification variable identifier pure state based unification
newtype UVar (t :: AHyperType) = UVar Int
    deriving stock (Generic, Show)
    deriving newtype (Eq, Ord)
Lens.makePrisms ''UVar

-- | The state of unification variables implemented in a pure data structure
newtype Binding t = Binding (Seq (UTerm UVar t))
    deriving stock Generic

Lens.makePrisms ''Binding
makeCommonInstances [''Binding]

-- | An empty 'Binding'
emptyBinding :: Binding t
emptyBinding = Binding mempty

-- | A 'BindingDict' for 'UVar's in a 'MonadState' whose state contains a 'Binding'
{-# INLINE bindingDict #-}
bindingDict ::
    MonadState s m =>
    ALens' s (Tree Binding t) ->
    BindingDict UVar m t
bindingDict l =
    BindingDict
    { lookupVar =
        \(UVar k) ->
        Lens.use (Lens.cloneLens l . _Binding)
        <&> (^?! Lens.ix k)
    , newVar =
        \x ->
        Lens.cloneLens l . _Binding <<%= (Sequence.|> x)
        <&> Sequence.length <&> UVar
    , bindVar =
        \(UVar k) v ->
        Lens.cloneLens l . _Binding . Lens.ix k .= v
    }
