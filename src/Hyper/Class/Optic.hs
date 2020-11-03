{-# LANGUAGE FlexibleContexts #-}

-- | A class for optics into child nodes.

module Hyper.Class.Optic
    ( HOptic(..)
    , HLens, HTraversal, HSetter, HPrism, HIso
    , hLens
    ) where

import Control.Lens
import Hyper.Type (type (#))

import Hyper.Internal.Prelude

class HOptic pc fc s a where
    hOptic ::
        (pc p, fc f) =>
        Proxy pc -> Proxy fc ->
        Optic' p f (s # h) (h # a)

type HLens = HOptic ((~) (->)) Functor
type HTraversal = HOptic ((~) (->)) Applicative
type HSetter = HOptic ((~) (->)) Settable
type HPrism = HOptic Choice Applicative
type HIso = HOptic Profunctor Functor

hLens :: HLens s a => Lens' (s # h) (h # a)
hLens = hOptic (Proxy @((~) (->))) (Proxy @Functor)
