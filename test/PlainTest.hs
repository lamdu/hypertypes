{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module PlainTest where

import Control.Exception (evaluate)
import Control.Lens
import GHC.Generics
import Hyper
import Test.Tasty
import Test.Tasty.HUnit

import Prelude

-- A direct single-constructor child must retain its `Pure` wrapper, even when
-- the child itself contains a container of sum nodes.  Flattening `Child`
-- into `Parent` used to make the generated `HasHPlain Parent` fail to typecheck.
data Parent (h :: AHyperType) = Parent (h :# Child)

data Child (h :: AHyperType) = Child [h :# (Leaf :+: Other)]

data Leaf (h :: AHyperType) = Leaf String

data Other (h :: AHyperType) = Other String

makeHasHPlain [''Parent, ''Child, ''Leaf, ''Other]

parentPlain :: HPlain Parent
parentPlain =
    hPlain
        # Pure
            ( Parent
                (Pure (Child [Pure (L1 (Leaf "leaf"))]))
            )

regression :: TestTree
regression =
    testCase "HasHPlain: direct child containing a sum" $ do
        _ <- evaluate parentPlain
        pure ()

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
