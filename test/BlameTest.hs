{-# LANGUAGE OverloadedStrings #-}

module BlameTest (test) where

import qualified Control.Lens as Lens
import Control.Lens.Operators
import ExprUtils
import Hyper
import Hyper.Infer.Blame
import Hyper.Recurse
import Hyper.Syntax (App (..), Var (..))
import Hyper.Unify.New
import LangB
import qualified LangBTest
import Test.Tasty
import Test.Tasty.HUnit

import Prelude

test :: TestTree
test =
    testGroup
        "blame"
        [ testBlame (addAnns (BAppP (BVarP "unitToUnit") (BLitP 5) ^. hPlain)) "--X"
        , testBlame
            ( Ann
                (Const @Int 2)
                ( BApp
                    ( App
                        (Ann (Const 1) (BVar (Var "unitToUnit")))
                        (Ann (Const 0) (BLit 5))
                    )
                )
            )
            "-X-"
        ]

testBlame :: (Ord a, Show a) => Annotated a # LangB -> String -> TestTree
testBlame term expect =
    case result of
        Left{} -> assertFailure "Unexpected type error in testBlame"
        Right x ->
            assertEqual "Wrong blame" expect formatted
            where
                formatted = x ^.. hflipped . hfolded1 . Lens._2 <&> fmt
        & testCase
            ( prettyStyle (unwrap (const (^. hVal)) term)
                <> " "
                <> show (term ^.. hflipped . hfolded1 . Lens._Wrapped)
            )
    where
        fmt Good{} = '-'
        fmt _ = 'X'
        result =
            do
                top <- newUnbound
                blame getConst (_ANode # top) term
                & LangBTest.withEnv id
                & execPureInferB
