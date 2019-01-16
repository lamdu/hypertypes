{-# LANGUAGE FlexibleContexts, TypeFamilies, BlockArguments, ScopedTypeVariables #-}

import           LangA.Pure
import           LangB.Pure
import           TypeLang.Pure
import           AST
import           AST.Class.Infer
import           AST.Class.Infer.Inferred
import           AST.Class.Infer.ScopeLevel
import           AST.Class.Recursive
import           AST.Class.Unify
import           AST.Term.NamelessScope
import           AST.Term.Nominal
import           AST.Term.Scheme
import           AST.Unify
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.ST
import           Data.Functor.Const
import           Data.Proxy
import           Data.STRef
import           System.Exit (exitFailure)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

lamXYx5 :: Tree Pure (LangA EmptyScope)
lamXYx5 = aLam \x -> aLam \_y -> x `aApp` (aLit 5 $:: intA)

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
            & Lens.at (Name "key") ?~ Pure TInt
            & Lens.at (Name "value") ?~ Pure TInt
            & QVarInstances
            & (`Types` QVarInstances mempty)
            & NominalInst (Name "Map")
            & TNom
            & Pure
            & uniType

letGen :: Tree Pure LangB
letGen = bLet "id" (lam "x" id) \i -> i $$ i $$ bLit 5

shouldNotGen :: Tree Pure LangB
shouldNotGen = lam "x" \x -> bLet "y" x id

record :: Tree Pure LangB
record = closedRec [("a", bLit 5)]

extendLit :: Tree Pure LangB
extendLit = recExtend [("a", bLit 5)] (bLit 7)

extendDup :: Tree Pure LangB
extendDup = closedRec [("a", bLit 7), ("a", bLit 5)]

extendGood :: Tree Pure LangB
extendGood = closedRec [("b", bLit 7), ("a", bLit 5)]

getAField :: Tree Pure LangB
getAField = lam "x" \x -> getField x "a"

unifyRows :: Tree Pure LangB
unifyRows =
    -- \f -> f {a : 5, b : 7} (f {b : 5, a : 7} 12)
    lam "f" \f ->
    (f $$ closedRec [("a", bLit 5), ("b", bLit 7)])
    $$
    ((f $$ closedRec [("b", bLit 5), ("a", bLit 7)]) $$ bLit 12)

inferExpr ::
    forall m t.
    ( Infer m t
    , Recursive Children t
    , Recursive (InferredChildConstraints (Recursive (Unify m))) t
    ) =>
    Tree Pure t ->
    m (Tree Pure (TypeOf t))
inferExpr x =
    inferNode (wrap (Proxy :: Proxy Children) (Ann ()) x)
    <&> Inferred
    >>= children (Proxy :: Proxy (Recursive (Unify m))) applyBindings
    <&> (^. _Inferred . iType)

execPureInferA :: PureInferA a -> Either (Tree TypeError Pure) a
execPureInferA (PureInferA act) =
    runRWST act (mempty, ScopeLevel 0) emptyPureInferState <&> (^. Lens._1)

execSTInferA :: STInferA s a -> ST s (Either (Tree TypeError Pure) a)
execSTInferA (STInferA act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, ScopeLevel 0, qvarGen) & runExceptT

execPureInferB :: PureInferB a -> Either (Tree TypeError Pure) a
execPureInferB (PureInferB act) =
    runRWST act emptyInferScope emptyPureInferState
    <&> (^. Lens._1)

execSTInferB :: STInferB s a -> ST s (Either (Tree TypeError Pure) a)
execSTInferB (STInferB act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (emptyInferScope, qvarGen) & runExceptT

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

testB :: Tree Pure LangB -> String -> IO Bool
testB expr expect =
    testCommon expr expect pureRes stRes
    where
        pureRes = execPureInferB (inferExpr expr)
        stRes = runST (execSTInferB (inferExpr expr))

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
            , testA infinite     "Left t0 occurs in itself, expands to: t0 -> t1"
            , testA skolem       "Left SkolemEscape t0"
            , testA validForAll  "Right (t0 -> t0)"
            , testA nomLam       "Right (Map[key: Int, value: Int] -> Map[key: Int, value: Int])"
            , testB letGen       "Right Int"
            , testB shouldNotGen "Right (t0 -> t0)"
            , testB record       "Right (a : Int :*: {})"
            , testB extendLit    "Left Mismatch Int r0"
            , testB extendDup    "Left ConstraintsViolation a : Int :*: {} Forbidden fields: [a]"
            , testB extendGood   "Right (b : Int :*: a : Int :*: {})"
            , testB unifyRows    "Right (((a : Int :*: b : Int :*: {}) -> Int -> Int) -> Int)"
            , testB getAField    "Right ((a : t0 :*: r0) -> t0)"
            ]

