-- | Lift Functors to HyperTypes
{-# LANGUAGE TemplateHaskell, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving #-}
module Hyper.Type.Functor
    ( F(..), _F, HWitness(..)
    ) where

import Control.Lens (Iso, iso, mapped)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Monad (HMonad(..))
import Hyper.Class.Nodes (HNodes(..), (#>))
import Hyper.Class.Recursive (RNodes, Recursively(..), RTraversable)
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (Tree, type (#))
import Hyper.Type.Combinator.Compose

import Prelude.Compat

-- | Lift a 'Functor', or type constructor of kind @Type -> Type@ to a 'Hyper.Type.HyperType'.
--
-- * @F Maybe@ can be used to encode structures with missing values
-- * @F (Either Text)@ can be used to encode results of parsing where structure components
--   may fail to parse.
newtype F f h = F (f (h # F f))
    deriving stock Generic

-- | An 'Iso' from 'F' to its content.
--
-- Using `_F` rather than the 'F' data constructor is recommended,
-- because it helps the type inference know that @F f@ is parameterized with a 'Hyper.Type.HyperType'.
_F ::
    Iso (Tree (F f0) k0)
        (Tree (F f1) k1)
        (f0 (Tree k0 (F f0)))
        (f1 (Tree k1 (F f1)))
_F = iso (\(F x) -> x) F

makeCommonInstances [''F]
makeHTraversableApplyAndBases ''F

instance Monad f => HMonad (F f) where
    hjoin =
        ( _F %~
            ( >>=
                ( mapped %~ t . (^. _Compose)
                ) . (^. _Compose . _F)
            )
        ) . (^. _Compose)
        where
            t ::
                forall p.
                Recursively HFunctor p =>
                Tree p (Compose (F f) (F f)) ->
                Tree p (F f)
            t =
                withDict (recursively (Proxy @(HFunctor p))) $
                hmap (Proxy @(Recursively HFunctor) #> hjoin)

instance RNodes (F f)
instance c (F f) => Recursively c (F f)
instance Traversable f => RTraversable (F f)
