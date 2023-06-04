{-# LANGUAGE OverloadedStrings #-}

module AlphaEqTest (test) where

import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.RWS
import Control.Monad.ST (runST)
import Data.Functor.Identity (Identity (..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import ExprUtils
import Hyper
import Hyper.Syntax.Scheme
import Hyper.Syntax.Scheme.AlphaEq (alphaEq)
import LangB
import Test.Tasty
import Test.Tasty.HUnit
import TypeLang

import Prelude

test :: TestTree
test =
    testGroup
        "alpha-eq"
        [ testAlphaEq (uniType TIntP) (uniType TIntP) True
        , testAlphaEq (uniType TIntP) intToInt False
        , testAlphaEq intToInt intToInt True
        , testAlphaEq (intsRecord ["a", "b"]) (intsRecord ["b", "a"]) True
        , testAlphaEq (intsRecord ["a", "b"]) (intsRecord ["b"]) False
        , testAlphaEq (intsRecord ["a", "b", "c"]) (intsRecord ["c", "b", "a"]) True
        , testAlphaEq (intsRecord ["a", "b", "c"]) (intsRecord ["b", "c", "a"]) True
        , testAlphaEq (forAll1 "a" id) (forAll1 "b" id) True
        , testAlphaEq (forAll1 "a" id) (uniType TIntP) False
        , testAlphaEq (forAll1r "a" TRecP) (uniType TIntP) False
        , testAlphaEq (forAll1r "a" TRecP) (forAll1r "b" TRecP) True
        , testAlphaEq (mkOpenRec "a" "x" "y") (mkOpenRec "b" "y" "x") True
        , testAlphaEq (valH0 (TVarP "a")) (valH0 (TRecP REmptyP)) False
        ]
    where
        valH0 x =
            TFunP (TVarP "a") (TRecP (RExtendP "t" x (RVarP "c"))) ^. hPlain
                & Scheme
                    ( Types
                        (QVars (mempty & Lens.at "a" ?~ mempty))
                        (QVars (mempty & Lens.at "c" ?~ RowConstraints (Set.fromList ["t"]) mempty))
                    )
                & Pure
        mkOpenRec a x y =
            _Pure
                # Scheme
                    ( Types
                        (QVars mempty)
                        (QVars (Map.fromList [(a, RowConstraints (Set.fromList [x, y]) mempty)]))
                    )
                    ( TRecP
                        ( RVarP a
                            & RExtendP x TIntP
                            & RExtendP y TIntP
                        )
                        ^. hPlain
                    )

testAlphaEq :: Pure # Scheme Types Typ -> Pure # Scheme Types Typ -> Bool -> TestTree
testAlphaEq x y expect =
    do
        assertEqual msg expect pureRes
        assertEqual ("ST: " <> msg) expect stRes
        & testCase (prettyStyle x <> sep <> prettyStyle y)
    where
        sep = if expect then " == " else " != "
        msg = "Alpha eq of " <> prettyStyle x <> " and " <> prettyStyle y
        pureRes = Lens.has Lens._Right (execPureInferB (alphaEq x y))
        stRes = Lens.has Lens._Right (runST (execSTInferB (alphaEq x y)))

uniType :: HPlain Typ -> Pure # Scheme Types Typ
uniType typ =
    _Pure
        # Scheme
            { _sForAlls = Types (QVars mempty) (QVars mempty)
            , _sTyp = typ ^. hPlain
            }

intsRecord :: [Name] -> Pure # Scheme Types Typ
intsRecord = uniType . TRecP . foldr (`RExtendP` TIntP) REmptyP

intToInt :: Pure # Scheme Types Typ
intToInt = TFunP TIntP TIntP & uniType

forAll1 ::
    Name ->
    (HPlain Typ -> HPlain Typ) ->
    Pure # Scheme Types Typ
forAll1 t body =
    forAll (Identity t) (Const ()) $ \(Identity tv) _ -> body tv

forAll1r ::
    Name ->
    (HPlain Row -> HPlain Typ) ->
    Pure # Scheme Types Typ
forAll1r t body =
    forAll (Const ()) (Identity t) $ \_ (Identity tv) -> body tv
