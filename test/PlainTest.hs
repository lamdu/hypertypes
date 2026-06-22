module PlainTest where

import Control.Lens
import Hyper
import Test.Tasty
import Test.Tasty.HUnit

import Prelude

test :: TestTree
test =
    assertEqual "hplain const" (hPlain # Pure (Const (5 :: Int)) & show) "ConstP 5"
    & testCase "show HPlain"
