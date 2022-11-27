{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Lift Functors to HyperTypes
module Hyper.Type.Functor
    ( F (..)
    , _F
    , W_F (..)
    ) where

import Control.Lens (iso, mapped)
import Hyper
import Hyper.Class.Monad (HMonad (..))

import Hyper.Internal.Prelude

-- | Lift a 'Functor', or type constructor of kind @Type -> Type@ to a 'Hyper.Type.HyperType'.
--
-- * @F Maybe@ can be used to encode structures with missing values
-- * @F (Either Text)@ can be used to encode results of parsing where structure components
--   may fail to parse.
newtype F f h = F (f (h :# F f))
    deriving stock (Generic)

-- | An 'Iso' from 'F' to its content.
--
-- Using `_F` rather than the 'F' data constructor is recommended,
-- because it helps the type inference know that @F f@ is parameterized with a 'Hyper.Type.HyperType'.
_F ::
    Iso
        (F f0 # k0)
        (F f1 # k1)
        (f0 (k0 # F f0))
        (f1 (k1 # F f1))
_F = iso (\(F x) -> x) F

makeCommonInstances [''F]
makeHTraversableApplyAndBases ''F

instance Monad f => HMonad (F f) where
    hjoin =
        ( _F
            %~ ( >>=
                    ( mapped %~ t . (^. _HCompose)
                    )
                        . (^. _HCompose . _F)
               )
        )
            . (^. _HCompose)
        where
            t ::
                forall p.
                Recursively HFunctor p =>
                p # HCompose (F f) (F f) ->
                p # F f
            t =
                hmap (Proxy @(Recursively HFunctor) #> hjoin)
                    \\ recursively (Proxy @(HFunctor p))

instance RNodes (F f)
instance c (F f) => Recursively c (F f)
instance Traversable f => RTraversable (F f)
