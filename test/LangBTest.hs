{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module LangBTest (test, withEnv) where

import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.RWS
import Control.Monad.ST (runST)
import Data.Functor.Identity (Identity (..))
import ExprUtils
import Hyper
import Hyper.Syntax.Nominal (NominalDecl (..), loadNominalDecl)
import Hyper.Syntax.Scheme
import Hyper.Unify
import LangB
import Test.Tasty
import TypeLang

import Prelude

test :: TestTree
test =
    testGroup
        "infer LangB"
        [ testB letGen0 "Right Int"
        , testB letGen1 "Right (∀t0(*). (Int -> Int -> t0) -> t0)"
        , testB letGen2 "Right (∀t0(*). ∀r0(∌ [a]). ∀r1(∌ [a]). (a : (a : t0 :*: r0) :*: r1) -> t0)"
        , testB genInf "Left (t0 occurs in itself, expands to: t0 -> t1)"
        , testB shouldNotGen "Right (∀t0(*). t0 -> t0)"
        , testB simpleRec "Right (a : Int :*: {})"
        , testB extendLit "Left (Mismatch Int r0)"
        , testB extendDup "Left (ConstraintsViolation (a : Int :*: {}) (∌ [a]))"
        , testB extendGood "Right (b : Int :*: a : Int :*: {})"
        , testB unifyRows "Right (((b : Int :*: a : Int :*: {}) -> Int -> Int) -> Int)"
        , testB openRows "Right (∀r0(∌ [a, b, c]). (c : Int :*: r0) -> (b : Int :*: r0) -> ((c : Int :*: a : Int :*: b : Int :*: r0) -> Int -> Int) -> Int)"
        , testB getAField "Right (∀t0(*). ∀r0(∌ [a]). (a : t0 :*: r0) -> t0)"
        , testB vecApp "Right (∀t0(*). t0 -> t0 -> Vec[elem: t0])"
        , testB usePhantom "Right (∀t0(*). PhantomInt[phantom: t0])"
        , testB return5 "Right (∀r0(*). Mut[value: Int, effects: r0])"
        , testB returnOk "Right LocalMut[value: Int]"
        , testB nomSkolem0 "Left (SkolemEscape: r0)"
        , testB nomSkolem1 "Left (SkolemEscape: r0)"
        ]

letGen0 :: HPlain LangB
letGen0 =
    BLetP "id" (BLamP "x" "x") $
        "id" `BAppP` "id" `BAppP` BLitP 5

letGen1 :: HPlain LangB
letGen1 =
    BLetP "five" (BLitP 5) $
        BLetP
            "f"
            (BLamP "x" ("x" `BAppP` "five" `BAppP` "five"))
            "f"

letGen2 :: HPlain LangB
letGen2 =
    BLetP "f" (BLamP "x" (BGetFieldP "x" "a")) $
        BLamP "x" ("f" `BAppP` ("f" `BAppP` "x"))

genInf :: HPlain LangB
genInf =
    BLetP
        "f"
        (BLamP "x" ("x" `BAppP` "x"))
        "f"

shouldNotGen :: HPlain LangB
shouldNotGen =
    BLamP
        "x"
        ( BLetP
            "y"
            "x"
            "y"
        )

simpleRec :: HPlain LangB
simpleRec =
    BRecExtendP
        "a"
        (BLitP 5)
        BRecEmptyP

extendLit :: HPlain LangB
extendLit =
    BRecExtendP "a" (BLitP 5) $
        BLitP 7

extendDup :: HPlain LangB
extendDup =
    BRecExtendP "a" (BLitP 7) $
        BRecExtendP
            "a"
            (BLitP 5)
            BRecEmptyP

extendGood :: HPlain LangB
extendGood =
    BRecExtendP "b" (BLitP 7) $
        BRecExtendP
            "a"
            (BLitP 5)
            BRecEmptyP

getAField :: HPlain LangB
getAField = BLamP "x" (BGetFieldP "x" "a")

vecApp :: HPlain LangB
vecApp =
    BLamP
        "x"
        ( BLamP
            "y"
            ( BToNomP "Vec" $
                BRecExtendP "x" "x" $
                    BRecExtendP
                        "y"
                        "y"
                        BRecEmptyP
            )
        )

usePhantom :: HPlain LangB
usePhantom = BToNomP "PhantomInt" (BLitP 5)

unifyRows :: HPlain LangB
unifyRows =
    BLamP "f" ("f" `BAppP` r0 `BAppP` ("f" `BAppP` r1 `BAppP` BLitP 12))
    where
        r0 =
            BRecExtendP "a" (BLitP 5) $
                BRecExtendP
                    "b"
                    (BLitP 7)
                    BRecEmptyP
        r1 =
            BRecExtendP "b" (BLitP 5) $
                BRecExtendP
                    "a"
                    (BLitP 7)
                    BRecEmptyP

openRows :: HPlain LangB
openRows =
    BLamP "x" $
        BLamP "y" $
            BLamP "f" $
                "f" `BAppP` r0 `BAppP` ("f" `BAppP` r1 `BAppP` BLitP 12)
    where
        r0 =
            BRecExtendP "a" (BLitP 5) $
                BRecExtendP "b" (BLitP 7) $
                    BVarP "x"
        r1 =
            BRecExtendP "c" (BLitP 5) $
                BRecExtendP "a" (BLitP 7) $
                    BVarP "y"

return5 :: HPlain LangB
return5 = "return" `BAppP` BLitP 5

returnOk :: HPlain LangB
returnOk = BToNomP "LocalMut" return5

nomSkolem0 :: HPlain LangB
nomSkolem0 = BLamP "x" (BToNomP "LocalMut" "x")

nomSkolem1 :: HPlain LangB
nomSkolem1 = nomSkolem0 `BAppP` return5

vecNominalDecl :: Pure # NominalDecl Typ
vecNominalDecl =
    _Pure
        # NominalDecl
            { _nParams =
                Types
                    { _tRow = mempty
                    , _tTyp = mempty & Lens.at "elem" ?~ mempty
                    }
            , _nScheme =
                Scheme
                    { _sForAlls = Types mempty mempty
                    , _sTyp =
                        ( REmptyP
                            & RExtendP "x" (TVarP "elem")
                            & RExtendP "y" (TVarP "elem")
                            & TRecP
                        )
                            ^. hPlain
                    }
            }

phantomIntNominalDecl :: Pure # NominalDecl Typ
phantomIntNominalDecl =
    _Pure
        # NominalDecl
            { _nParams =
                Types
                    { _tRow = mempty
                    , _tTyp = mempty & Lens.at "phantom" ?~ mempty
                    }
            , _nScheme =
                Scheme
                    { _sForAlls = Types mempty mempty
                    , _sTyp = _Pure # TInt
                    }
            }

mutType :: HPlain Typ
mutType =
    TNomP
        "Mut"
        Types
            { _tRow = mempty & Lens.at "effects" ?~ (RVar "effects" & Pure) & QVarInstances
            , _tTyp = mempty & Lens.at "value" ?~ (TVar "value" & Pure) & QVarInstances
            }

-- A nominal type with foralls:
-- "newtype LocalMut a = forall s. Mut s a"
localMutNominalDecl :: Pure # NominalDecl Typ
localMutNominalDecl =
    _Pure
        # NominalDecl
            { _nParams =
                Types
                    { _tRow = mempty
                    , _tTyp = mempty & Lens.at "value" ?~ mempty
                    }
            , _nScheme =
                forAll (Const ()) (Identity "effects") (\_ _ -> mutType) ^. _Pure
            }

returnScheme :: Pure # Scheme Types Typ
returnScheme =
    forAll (Identity "value") (Identity "effects") (\(Identity val) _ -> TFunP val mutType)

unitToUnitScheme :: Pure # Scheme Types Typ
unitToUnitScheme =
    forAll Proxy Proxy (\Proxy Proxy -> TFunP (TRecP REmptyP) (TRecP REmptyP))

withEnv ::
    ( UnifyGen m Row
    , MonadReader env m
    , HasScheme Types m Typ
    ) =>
    Lens.LensLike' Identity env (InferScope (UVarOf m)) ->
    m a ->
    m a
withEnv l act =
    do
        vec <- loadNominalDecl vecNominalDecl
        phantom <- loadNominalDecl phantomIntNominalDecl
        localMut <- loadNominalDecl localMutNominalDecl
        let addNoms x =
                x
                    & Lens.at "Vec" ?~ vec
                    & Lens.at "PhantomInt" ?~ phantom
                    & Lens.at "LocalMut" ?~ localMut
        ret <- loadScheme returnScheme
        unitToUnit <- loadScheme unitToUnitScheme
        let addEnv x =
                x
                    & nominals %~ addNoms
                    & varSchemes . _ScopeTypes . Lens.at "return" ?~ MkHFlip ret
                    & varSchemes . _ScopeTypes . Lens.at "unitToUnit" ?~ MkHFlip unitToUnit
        local (l %~ addEnv) act

testB :: HPlain LangB -> String -> TestTree
testB p expect =
    testCommon expr expect pureRes stRes
    where
        expr = p ^. hPlain
        pureRes = execPureInferB (withEnv id (inferExpr expr))
        stRes = runST (execSTInferB (withEnv Lens._1 (inferExpr expr)))
