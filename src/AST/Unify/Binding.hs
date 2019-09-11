{-# LANGUAGE UndecidableInstances, TemplateHaskell, GeneralizedNewtypeDeriving #-}

module AST.Unify.Binding
    ( UVar(..), _UVar
    , Binding(..), _Binding
    , emptyBinding
    , bindingDict
    ) where

import           AST.Class.Unify (BindingDict(..))
import           AST.Knot (Tree, Knot)
import           AST.TH.Internal.Instances (makeCommonInstances)
import           AST.Unify.Term
import           Control.Lens (ALens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.State (MonadState(..))
import           Data.Sequence
import qualified Data.Sequence as Sequence
import           GHC.Generics (Generic)

import           Prelude.Compat

newtype UVar (t :: Knot) = UVar Int
    deriving stock (Generic, Show)
    deriving newtype (Eq, Ord)
Lens.makePrisms ''UVar

newtype Binding t = Binding (Seq (UTerm UVar t))
    deriving stock Generic

Lens.makePrisms ''Binding
makeCommonInstances [''Binding]

emptyBinding :: Binding t
emptyBinding = Binding mempty

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
