{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module PlainTest where

import Control.Lens
import Data.Proxy
import GHC.Generics
import Hyper
import Test.Tasty
import Test.Tasty.HUnit

import Prelude

newtype PureB h = PureB (h :# PureB)
    deriving stock (Generic)
makeHasHPlain [''PureB]

type IgnoreChild (child :: HyperType) x = Int

data EmbeddedGadt h where
    EmbeddedGadt :: IgnoreChild child Bool -> EmbeddedGadt # child

newtype EmbedsGadt h = EmbedsGadt (EmbeddedGadt h)
    deriving stock (Generic)
makeHasHPlain [''EmbedsGadt]

newtype EmbeddedData h = EmbeddedData (Proxy (GetHyperType h))

newtype EmbedsData h = EmbedsData (EmbeddedData h)
    deriving stock (Generic)
makeHasHPlain [''EmbedsData]

newtype HasPureC h = HasPureC (h :# PureC)
    deriving stock (Generic)
newtype PureC h = PureC (h :# PureC)
    deriving stock (Generic)
makeHasHPlain [''HasPureC, ''PureC]

test :: TestTree
test =
    do
        assertEqual "hplain const" (hPlain # Pure (Const (5 :: Int)) & show) "ConstP 5"
        assertEqual
            "hplain prod"
            (hPlain # Pure (Const (5 :: Int) :*: Const "hello") & show)
            "ProdP (ConstP 5) (ConstP \"hello\")"
        assertEqual
            "hplain sum"
            (hPlain # Pure (L1 (Const (5 :: Int)) :: (Const Int :+: Const String) # Pure) & show)
            "L1P (ConstP 5)"
        & testCase "show HPlain"
