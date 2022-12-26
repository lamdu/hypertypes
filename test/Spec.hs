{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Except
import Control.Monad.RWS
import Control.Monad.ST (runST)
import Data.Constraint ((\\))
import Data.Functor.Identity (Identity (..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Hyper
import Hyper.Infer
import Hyper.Infer.Blame (BlameResult (Good), blame)
import Hyper.Recurse (wrap)
import Hyper.Syntax (App (..), Var (..))
import Hyper.Syntax.NamelessScope (EmptyScope)
import Hyper.Syntax.Nominal (NominalDecl (..), loadNominalDecl)
import Hyper.Syntax.Scheme
import Hyper.Syntax.Scheme.AlphaEq (alphaEq)
import Hyper.Unify
import Hyper.Unify.Generalize (generalize)
import Hyper.Unify.New (newUnbound)
import Hyper.Unify.QuantifiedVar (HasQuantifiedVar (..))
import LangA
import LangB
import System.Exit (exitFailure)
import qualified Text.PrettyPrint as Pretty
import Text.PrettyPrint.HughesPJClass (Pretty (..))
import TypeLang

import Prelude

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

addAnns :: Recursively HFunctor h => Pure # h -> Ann (Const ()) # h
addAnns = wrap (const (Ann (Const ())))

inferExpr ::
    forall m t.
    ( HasInferredType t
    , Infer m t
    , HasScheme Types m (TypeOf t)
    , RTraversable t
    , Recursively (InferOfConstraint HFoldable) t
    ) =>
    Pure # t ->
    m (Pure # Scheme Types (TypeOf t))
inferExpr x =
    do
        inferRes <- infer (addAnns x)
        result <-
            inferRes ^# hAnn . Lens._2 . _InferResult . inferredType (Proxy @t)
                & generalize
                >>= saveScheme
        result
            <$ htraverse_
                ( Proxy @(Infer m) #*#
                    Proxy @(Recursively (InferOfConstraint HFoldable)) #*#
                        \(w :: HWitness (HFlip Ann t) n) (Const () :*: InferResult i) ->
                            htraverse_ (Proxy @(UnifyGen m) #> void . applyBindings) i
                                \\ inferContext (Proxy @m) w
                                \\ inferOfConstraint @HFoldable w
                                \\ recursively (Proxy @(InferOfConstraint HFoldable n))
                )
                (_HFlip # inferRes)

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

prettyStyle :: Pretty a => a -> String
prettyStyle = Pretty.renderStyle (Pretty.Style Pretty.OneLineMode 0 0) . pPrint

prettyPrint :: Pretty a => a -> IO ()
prettyPrint = putStrLn . prettyStyle

testCommon ::
    (Pretty (lang # Pure), Pretty a, Eq a) =>
    Pure # lang ->
    String ->
    Either (TypeError # Pure) a ->
    Either (TypeError # Pure) a ->
    IO Bool
testCommon expr expect pureRes stRes =
    do
        putStrLn ""
        prettyPrint expr
        putStrLn "inferred to:"
        prettyPrint pureRes
        filter (not . fst) checks <&> snd & sequence_
        all fst checks & pure
    where
        checks =
            [ (expect == prettyStyle pureRes, putStrLn ("FAIL! Expected:\n" <> expect))
            , (pureRes == stRes, putStrLn "FAIL! Different result in ST:" *> prettyPrint stRes)
            ]

testA :: HPlain (LangA EmptyScope) -> String -> IO Bool
testA p expect =
    testCommon expr expect pureRes stRes
    where
        expr = p ^. hPlain
        pureRes = execPureInferA (inferExpr expr)
        stRes = runST (execSTInferA (inferExpr expr))

testB :: HPlain LangB -> String -> IO Bool
testB p expect =
    testCommon expr expect pureRes stRes
    where
        expr = p ^. hPlain
        pureRes = execPureInferB (withEnv id (inferExpr expr))
        stRes = runST (execSTInferB (withEnv Lens._1 (inferExpr expr)))

testAlphaEq :: Pure # Scheme Types Typ -> Pure # Scheme Types Typ -> Bool -> IO Bool
testAlphaEq x y expect =
    do
        putStrLn ""
        prettyPrint (x, y)
        putStrLn ("Alpha Eq: " <> show pureRes)
        when (pureRes /= expect) (putStrLn "WRONG!")
        putStrLn ("Alpha Eq: " <> show stRes)
        when (stRes /= expect) (putStrLn "WRONG!")
        pure (pureRes == expect && stRes == expect)
    where
        pureRes = Lens.has Lens._Right (execPureInferB (alphaEq x y))
        stRes = Lens.has Lens._Right (runST (execSTInferB (alphaEq x y)))

testBlame :: Ord a => Annotated a # LangB -> String -> IO Bool
testBlame term expect =
    case result of
        Left{} -> False <$ putStrLn "Unexpected type error in testBlame"
        Right x ->
            do
                putStrLn ""
                putStrLn formatted
                when (formatted /= expect) (putStrLn ("Expected:" <> expect))
                pure (formatted == expect)
            where
                formatted = x ^.. hflipped . hfolded1 . Lens._2 <&> fmt
    where
        fmt Good{} = '-'
        fmt _ = 'X'
        result =
            do
                top <- newUnbound
                blame getConst (_ANode # top) term
                & withEnv id
                & execPureInferB

intsRecord :: [Name] -> Pure # Scheme Types Typ
intsRecord = uniType . TRecP . foldr (`RExtendP` TIntP) REmptyP

intToInt :: Pure # Scheme Types Typ
intToInt = TFunP TIntP TIntP & uniType

uniType :: HPlain Typ -> Pure # Scheme Types Typ
uniType typ =
    _Pure
        # Scheme
            { _sForAlls = Types (QVars mempty) (QVars mempty)
            , _sTyp = typ ^. hPlain
            }

forAll ::
    (Traversable t, Traversable u) =>
    t Name ->
    u Name ->
    (t (HPlain Typ) -> u (HPlain Row) -> HPlain Typ) ->
    Pure # Scheme Types Typ
forAll tvs rvs body =
    _Pure
        # Scheme
            (Types (foralls tvs) (foralls rvs))
            (body (tvs <&> TVarP) (rvs <&> RVarP) ^. hPlain)
    where
        foralls ::
            ( Foldable f
            , QVar typ ~ Name
            , Monoid (TypeConstraintsOf typ)
            ) =>
            f Name ->
            QVars # typ
        foralls xs =
            xs ^.. Lens.folded
                <&> (,mempty)
                & Map.fromList
                & QVars

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

main :: IO ()
main =
    do
        numFails <-
            sequenceA tests
                <&> filter not
                <&> length
        putStrLn ""
        show numFails <> " tests failed out of " <> show (length tests) & putStrLn
        when (numFails > 0) exitFailure
    where
        tests =
            [ testA lamXYx5 "Right (∀t0(*). ∀t1(*). (Int -> t0) -> t1 -> t0)"
            , testA infinite "Left (t0 occurs in itself, expands to: t0 -> t1)"
            , testA skolem "Left (SkolemEscape: t0)"
            , testA validForAll "Right (∀t0(*). t0 -> t0)"
            , testA nomLam "Right (Map[key: Int, value: Int] -> Map[key: Int, value: Int])"
            , testB letGen0 "Right Int"
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
            , testAlphaEq (uniType TIntP) (uniType TIntP) True
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
            , testBlame (addAnns (BAppP (BVarP "unitToUnit") (BLitP 5) ^. hPlain)) "--X"
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
        valH0 x =
            TFunP (TVarP "a") (TRecP (RExtendP "t" x (RVarP "c"))) ^. hPlain
                & Scheme
                    ( Types
                        (QVars (mempty & Lens.at "a" ?~ mempty))
                        (QVars (mempty & Lens.at "c" ?~ RowConstraints (Set.fromList ["t"]) mempty))
                    )
                & Pure
