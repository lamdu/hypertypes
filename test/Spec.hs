{-# LANGUAGE FlexibleContexts, BlockArguments, OverloadedStrings #-}

import           Hyper
import           Hyper.Class.Unify
import           Hyper.Type.Combinator.Flip
import           Hyper.Infer
import           Hyper.Recurse
import           Hyper.Type.AST.NamelessScope (EmptyScope)
import           Hyper.Type.AST.Nominal
import           Hyper.Type.AST.Scheme
import           Hyper.Type.AST.Scheme.AlphaEq
import           Hyper.Unify.Apply
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.ST
import qualified Data.Map as Map
import           Data.Proxy
import qualified Data.Set as Set
import           LangA.Pure
import           LangB
import           ReadMeExamples ()
import           System.Exit (exitFailure)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import           TypeLang.Pure

import           Prelude

lamXYx5 :: Tree Pure (LangA EmptyScope)
lamXYx5 = aLam \x -> aLam \_y -> x `aApp` ((5 &# ALit) $:: uniType TIntP)

infinite :: Tree Pure (LangA EmptyScope)
infinite = aLam \x -> x `aApp` x

skolem :: Tree Pure (LangA EmptyScope)
skolem = aLam \x -> x $:: forAll1 "a" \a -> a

validForAll :: Tree Pure (LangA EmptyScope)
validForAll = aLam id $:: forAll1 "a" \a -> a ~> a

nomLam :: Tree Pure (LangA EmptyScope)
nomLam =
    aLam \x -> x $:: s
    where
        s =
            mempty
            & Lens.at "key" ?~ _Pure # TInt
            & Lens.at "value" ?~ _Pure # TInt
            & QVarInstances
            & (`Types` QVarInstances mempty)
            & TNomP "Map"
            & uniType

letGen0 :: HPlain LangB
letGen0 =
    BLetP "id" (BLamP "x" "x") $
    "id" `BAppP` "id" `BAppP` BLitP 5

letGen1 :: HPlain LangB
letGen1 =
    BLetP "five" (BLitP 5) $
    BLetP "f" (BLamP "x" ("x" `BAppP` "five" `BAppP` "five")) $
    "f"

letGen2 :: HPlain LangB
letGen2 =
    BLetP "f" (BLamP "x" (BGetFieldP "x" "a")) $
    BLamP "x" ("f" `BAppP` ("f" `BAppP` "x"))

genInf :: HPlain LangB
genInf =
    BLetP "f" (BLamP "x" ("x" `BAppP` "x"))
    "f"

shouldNotGen :: HPlain LangB
shouldNotGen =
    BLamP "x"
    ( BLetP "y" "x"
        "y"
    )

simpleRec :: HPlain LangB
simpleRec =
    BRecExtendP "a" (BLitP 5) $
    BRecEmptyP

extendLit :: HPlain LangB
extendLit =
    BRecExtendP "a" (BLitP 5) $
    BLitP 7

extendDup :: HPlain LangB
extendDup =
    BRecExtendP "a" (BLitP 7) $
    BRecExtendP "a" (BLitP 5) $
    BRecEmptyP

extendGood :: HPlain LangB
extendGood =
    BRecExtendP "b" (BLitP 7) $
    BRecExtendP "a" (BLitP 5) $
    BRecEmptyP

getAField :: HPlain LangB
getAField = BLamP "x" (BGetFieldP "x" "a")

vecApp :: HPlain LangB
vecApp =
    BLamP "x"
    ( BLamP "y"
        ( BToNomP "Vec" $
            BRecExtendP "x" "x" $
            BRecExtendP "y" "y" $
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
            BRecExtendP "b" (BLitP 7) $
            BRecEmptyP
        r1 =
            BRecExtendP "b" (BLitP 5) $
            BRecExtendP "a" (BLitP 7) $
            BRecEmptyP

return5 :: HPlain LangB
return5 = "return" `BAppP` BLitP 5

returnOk :: HPlain LangB
returnOk = BToNomP "LocalMut" return5

nomSkolem0 :: HPlain LangB
nomSkolem0 = BLamP "x" (BToNomP "LocalMut" "x")

nomSkolem1 :: HPlain LangB
nomSkolem1 = nomSkolem0 `BAppP` return5

inferExpr ::
    forall m t.
    ( HasInferredType t
    , Infer m t
    , RTraversable t
    , RTraversableInferOf t
    , InferredVarsConstraint (Unify m) t
    ) =>
    Tree Pure t ->
    m (Tree Pure (TypeOf t))
inferExpr x =
    infer (wrap (const (Ann ())) x)
    >>= Lens.from _Flip (traverseH (Proxy @(Unify m) #> applyBindings))
    <&> (^# iRes . inferredType (Proxy @t))

vecNominalDecl :: Tree Pure (NominalDecl Typ)
vecNominalDecl =
    _Pure # NominalDecl
    { _nParams =
        Types
        { _tRow = mempty
        , _tTyp = mempty & Lens.at "elem" ?~ mempty
        }
    , _nScheme =
        Scheme
        { _sForAlls = Types mempty mempty
        , _sTyp = record [("x", "elem" &# TVar), ("y", "elem" &# TVar)]
        }
    }

phantomIntNominalDecl :: Tree Pure (NominalDecl Typ)
phantomIntNominalDecl =
    _Pure # NominalDecl
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

mutType :: Tree Pure Typ
mutType =
    NominalInst "Mut"
    Types
    { _tRow = mempty & Lens.at "effects" ?~ ("effects" &# RVar) & QVarInstances
    , _tTyp = mempty & Lens.at "value" ?~ ("value" &# TVar) & QVarInstances
    }
    &# TNom

-- A nominal type with foralls:
-- "newtype LocalMut a = forall s. Mut s a"
localMutNominalDecl :: Tree Pure (NominalDecl Typ)
localMutNominalDecl =
    _Pure # NominalDecl
    { _nParams =
        Types
        { _tRow = mempty
        , _tTyp = mempty & Lens.at "value" ?~ mempty
        }
    , _nScheme =
        forAll (Lens.Const ()) (Lens.Identity "effects") (\_ _ -> mutType) ^. _Pure
    }

returnScheme :: Tree Pure (Scheme Types Typ)
returnScheme =
    forAll (Lens.Identity "value") (Lens.Identity "effects") $
    \(Lens.Identity val) _ -> val ~> mutType

withEnv ::
    ( Unify m Row, MonadReader env m
    , HasScheme Types m Typ
    ) =>
    Lens.LensLike' Lens.Identity env (InferScope (UVarOf m)) -> m a -> m a
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
        let addEnv x =
                x
                & nominals %~ addNoms
                & varSchemes . _ScopeTypes . Lens.at "return" ?~ ret
        local (l %~ addEnv) act

prettyPrint :: Pretty a => a -> IO ()
prettyPrint = print . pPrint

testCommon ::
    (Pretty (Tree lang Pure)) =>
    Tree Pure lang ->
    String ->
    Either (Tree TypeError Pure) (Tree Pure Typ) ->
    Either (Tree TypeError Pure) (Tree Pure Typ) ->
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
            [ (Pretty.text expect == pPrint pureRes, putStrLn ("FAIL! Expected:\n" <> expect))
            , (pureRes == stRes, putStrLn "FAIL! Different result in ST:" *> prettyPrint stRes)
            ]

testA :: Tree Pure (LangA EmptyScope) -> String -> IO Bool
testA expr expect =
    testCommon expr expect pureRes stRes
    where
        pureRes = execPureInferA (inferExpr expr)
        stRes = runST (execSTInferA (inferExpr expr))

testB :: HPlain LangB -> String -> IO Bool
testB p expect =
    testCommon expr expect pureRes stRes
    where
        expr = p ^. hPlain
        pureRes = execPureInferB (withEnv id (inferExpr expr))
        stRes = runST (execSTInferB (withEnv Lens._1 (inferExpr expr)))

testAlphaEq :: Tree Pure (Scheme Types Typ) -> Tree Pure (Scheme Types Typ) -> Bool -> IO Bool
testAlphaEq x y expect =
    do
        putStrLn ""
        prettyPrint (x, y)
        putStrLn ("Alpha Eq: " ++ show pureRes)
        when (pureRes /= expect) (putStrLn "WRONG!")
        putStrLn ("Alpha Eq: " ++ show stRes)
        when (stRes /= expect) (putStrLn "WRONG!")
        return (pureRes == expect && stRes == expect)
    where
        pureRes = Lens.has Lens._Right (execPureInferB (alphaEq x y))
        stRes = Lens.has Lens._Right (runST (execSTInferB (alphaEq x y)))

intsRecord :: [Name] -> Tree Pure (Scheme Types Typ)
intsRecord = uniType . (hPlain #) . record . map (, _Pure # TInt)

intToInt :: Tree Pure (Scheme Types Typ)
intToInt = TFunP TIntP TIntP & uniType

main :: IO ()
main =
    do
        numFails <-
            sequenceA tests
            <&> filter not <&> length
        putStrLn ""
        show numFails <> " tests failed out of " <> show (length tests) & putStrLn
        when (numFails > 0) exitFailure
    where
        tests =
            [ testA lamXYx5      "Right ((Int -> t0) -> t1 -> t0)"
            , testA infinite     "Left (t0 occurs in itself, expands to: t0 -> t1)"
            , testA skolem       "Left (SkolemEscape: t0)"
            , testA validForAll  "Right (t0 -> t0)"
            , testA nomLam       "Right (Map[key: Int, value: Int] -> Map[key: Int, value: Int])"
            , testB letGen0      "Right Int"
            , testB letGen1      "Right ((Int -> Int -> t0) -> t0)"
            , testB letGen2      "Right ((a : (a : t0 :*: r0) :*: r1) -> t0)"
            , testB genInf       "Left (t0 occurs in itself, expands to: t0 -> t1)"
            , testB shouldNotGen "Right (t0 -> t0)"
            , testB simpleRec    "Right (a : Int :*: {})"
            , testB extendLit    "Left (Mismatch Int r0)"
            , testB extendDup    "Left (ConstraintsViolation (a : Int :*: {}) (Forbidden fields: [a]))"
            , testB extendGood   "Right (b : Int :*: a : Int :*: {})"
            , testB unifyRows    "Right (((b : Int :*: a : Int :*: {}) -> Int -> Int) -> Int)"
            , testB getAField    "Right ((a : t0 :*: r0) -> t0)"
            , testB vecApp       "Right (t0 -> t0 -> Vec[elem: t0])"
            , testB usePhantom   "Right PhantomInt[phantom: t0]"
            , testB return5      "Right Mut[value: Int, effects: r0]"
            , testB returnOk     "Right LocalMut[value: Int]"
            , testB nomSkolem0   "Left (SkolemEscape: r0)"
            , testB nomSkolem1   "Left (SkolemEscape: r0)"
            , testAlphaEq (uniType TIntP) (uniType TIntP) True
            , testAlphaEq (uniType TIntP) intToInt False
            , testAlphaEq intToInt intToInt True
            , testAlphaEq (intsRecord ["a", "b"]) (intsRecord ["b", "a"]) True
            , testAlphaEq (intsRecord ["a", "b"]) (intsRecord ["b"]) False
            , testAlphaEq (intsRecord ["a", "b", "c"]) (intsRecord ["c", "b", "a"]) True
            , testAlphaEq (intsRecord ["a", "b", "c"]) (intsRecord ["b", "c", "a"]) True
            , testAlphaEq (forAll1 "a" id) (forAll1 "b" id) True
            , testAlphaEq (forAll1 "a" id) (uniType TIntP) False
            , testAlphaEq (forAll1r "a" (&# TRec)) (uniType TIntP) False
            , testAlphaEq (forAll1r "a" (&# TRec)) (forAll1r "b" (&# TRec)) True
            , testAlphaEq (mkOpenRec "a" "x" "y") (mkOpenRec "b" "y" "x") True
            ]
        mkOpenRec a x y =
            _Pure #
            Scheme
            (Types (QVars mempty)
                (QVars (Map.fromList [(a, RowConstraints (Set.fromList [x, y]) mempty)])))
            (rowExtends (a &# RVar) [(x, _Pure # TInt), (y, _Pure # TInt)] &# TRec)
