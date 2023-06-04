{-# LANGUAGE OverloadedStrings #-}

module LangATest (test) where

import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.RWS
import Control.Monad.ST (runST)
import ExprUtils
import Hyper
import Hyper.Syntax.NamelessScope (EmptyScope)
import Hyper.Syntax.Scheme
import LangA
import Test.Tasty
import TypeLang

import Prelude

test :: TestTree
test =
    testGroup
        "infer LangA"
        [ testA lamXYx5 "Right (∀t0(*). ∀t1(*). (Int -> t0) -> t1 -> t0)"
        , testA infinite "Left (t0 occurs in itself, expands to: t0 -> t1)"
        , testA skolem "Left (SkolemEscape: t0)"
        , testA validForAll "Right (∀t0(*). t0 -> t0)"
        , testA nomLam "Right (Map[key: Int, value: Int] -> Map[key: Int, value: Int])"
        ]

testA :: HPlain (LangA EmptyScope) -> String -> TestTree
testA p expect =
    testCommon expr expect pureRes stRes
    where
        expr = p ^. hPlain
        pureRes = execPureInferA (inferExpr expr)
        stRes = runST (execSTInferA (inferExpr expr))

lamXYx5 :: HPlain (LangA EmptyScope)
lamXYx5 =
    -- λx y. x 5
    ALamP (ALamP (AVarP (Just Nothing) `AAppP` ALitP 5))

infinite :: HPlain (LangA EmptyScope)
infinite =
    -- λx. x x
    ALamP (AVarP Nothing `AAppP` AVarP Nothing)

skolem :: HPlain (LangA EmptyScope)
skolem =
    -- λx. (x : ∀a. a)
    ALamP
        ( ATypeSigP
            (AVarP Nothing)
            (Types (QVars (mempty & Lens.at "a" ?~ mempty)) (QVars mempty))
            (TVarP "a")
        )

validForAll :: HPlain (LangA EmptyScope)
validForAll =
    -- (λx. x) : ∀a. a -> a
    ATypeSigP
        (ALamP (AVarP Nothing))
        (Types (QVars (mempty & Lens.at "a" ?~ mempty)) (QVars mempty))
        (TVarP "a" `TFunP` TVarP "a")

nomLam :: HPlain (LangA EmptyScope)
nomLam =
    -- λx. (x : Map[key: Int, value: Int])
    ALamP
        ( ATypeSigP
            (AVarP Nothing)
            (Types (QVars mempty) (QVars mempty))
            ( TNomP
                "Map"
                ( Types
                    ( QVarInstances
                        ( mempty
                            & Lens.at "key" ?~ Pure TInt
                            & Lens.at "value" ?~ Pure TInt
                        )
                    )
                    (QVarInstances mempty)
                )
            )
        )
