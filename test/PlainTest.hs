module PlainTest where

import Control.Lens
import GHC.Generics
import Hyper
import Test.Tasty
import Test.Tasty.HUnit

import Prelude

test :: TestTree
test =
    do
        assertEqual "hplain const" (hPlain # Pure (Const (5 :: Int)) & show) "ConstP 5"
        assertEqual "hplain prod"
            (hPlain # Pure (Const (5 :: Int) :*: Const "hello") & show)
            "ProdP (ConstP 5) (ConstP \"hello\")"
        assertEqual "hplain sum"
            (hPlain # Pure (L1 (Const (5 :: Int)) :: (Const Int :+: Const String) # Pure) & show)
            "L1P (ConstP 5)"
        & testCase "show HPlain"
