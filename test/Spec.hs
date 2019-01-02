{-# LANGUAGE FlexibleContexts #-}

import           LangA
import           LangB
import           TypeLang

import           AST
import           AST.Class.Infer
import           AST.Class.Infer.ScopeLevel
import           AST.Class.Recursive
import           AST.Term.Apply
import           AST.Term.FuncType
import           AST.Term.Lam
import           AST.Term.Let
import           AST.Term.RowExtend
import           AST.Term.Scheme
import           AST.Term.Scope
import           AST.Term.TypeSig
import           AST.Term.Var
import           AST.Unify
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.Trans.Maybe
import           Data.Functor.Const
import           Data.Proxy
import           Data.STRef
import           System.Exit (exitFailure)
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

var :: DeBruijnIndex k => Int -> Tree Pure (LangA k)
var = Pure . AVar . scopeVar

uniType :: Tree Pure Typ -> Tree Pure (Scheme Types Typ)
uniType typ =
    Pure Scheme
    { _sForAlls = Types (Vars []) (Vars [])
    , _sTyp = typ
    }

lamXYx5 :: Tree Pure (LangA EmptyScope)
lamXYx5 =
    -- \x y -> x (5 :: Int)
    Pure . ALam . scope $ \x ->
    Pure . ALam . scope $ \_y ->
    Pure TInt & uniType
    & TypeSig (Pure (ALit 5))
    & ATypeSig & Pure
    & Apply (var x) & AApp & Pure

infinite :: Tree Pure (LangA EmptyScope)
infinite =
    -- \x -> x x
    Pure . ALam . scope $ \x ->
    Apply (var x) (var x) & AApp & Pure

skolem :: Tree Pure (LangA EmptyScope)
skolem =
    -- \x -> (x :: forall a. a)
    -- TODO: This doesn't get pretty printed with parens!
    Pure . ALam . scope $ \x ->
    TVar "a" & Pure
    & Scheme (Types (Vars ["a"]) (Vars [])) & Pure
    & TypeSig (var x) & ATypeSig & Pure

validForAll :: Tree Pure (LangA EmptyScope)
validForAll =
    -- (\x -> x) :: forall a. a
    -- TODO: This doesn't get pretty printed with parens!
    FuncType (Pure (TVar "a")) (Pure (TVar "a"))
    & TFun & Pure
    & Scheme (Types (Vars ["a"]) (Vars [])) & Pure
    & TypeSig (scope var & ALam & Pure)
    & ATypeSig & Pure

lam :: String -> (Tree Pure LangB -> Tree Pure LangB) -> Tree Pure LangB
lam v mk = Var v & BVar & Pure & mk & Lam v & BLam & Pure

($$) :: Tree Pure LangB -> Tree Pure LangB -> Tree Pure LangB
x $$ y = Apply x y & BApp & Pure

bLit :: Int -> Tree Pure LangB
bLit = Pure . BLit

letGen :: Tree Pure LangB
letGen =
    -- let id x = x in id id 5
    (i $$ i) $$ bLit 5
    & Let "id" (lam "x" id) & BLet & Pure
    where
        i = Var "id" & BVar & Pure

shouldNotGen :: Tree Pure LangB
shouldNotGen =
    -- (\x -> let y = x in y)
    lam "x" $ \x ->
    Var "y" & BVar & Pure
    & Let "y" x & BLet & Pure

recExtend :: [(String, Tree Pure LangB)] -> Tree Pure LangB -> Tree Pure LangB
recExtend fields rest = foldr (fmap (Pure . BRecExtend) . uncurry RowExtend) rest fields

closedRec :: [(String, Tree Pure LangB)] -> Tree Pure LangB
closedRec fields = recExtend fields (Pure BRecEmpty)

record :: Tree Pure LangB
record =
    -- {a: 5}
    closedRec [("a", bLit 5)]

extendLit :: Tree Pure LangB
extendLit =
    -- {a: 5 | 7}
    recExtend [("a", bLit 5)] (bLit 7)

extendDup :: Tree Pure LangB
extendDup =
    -- {a: 7 | a : 5}
    recExtend [("a", bLit 7)] record

extendGood :: Tree Pure LangB
extendGood =
    -- {b: 7 | a : 5}
    recExtend [("b", bLit 7)] record

unifyRows :: Tree Pure LangB
unifyRows =
    -- \f -> f {a : 5, b : 7} (f {b : 5, a : 7} 12)
    lam "f" $ \f ->
    (f $$ closedRec [("a", bLit 5), ("b", bLit 7)])
    $$
    ((f $$ closedRec [("b", bLit 5), ("a", bLit 7)]) $$ bLit 12)

inferExpr ::
    (Infer m t, Recursive Children t) =>
    Tree Pure t ->
    m (Tree Pure (TypeAST t))
inferExpr x =
    inferNode (wrap (Proxy :: Proxy Children) (Ann ()) x)
    <&> (^. nodeType)
    >>= applyBindings

execPureInferA :: PureInferA a -> Maybe a
execPureInferA (PureInferA act) =
    runRWST act (mempty, ScopeLevel 0) emptyPureInferState <&> (^. Lens._1)

execSTInferA :: STInferA s a -> ST s (Maybe a)
execSTInferA (STInferA act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, ScopeLevel 0, qvarGen) & runMaybeT

execPureInferB :: PureInferB a -> Maybe a
execPureInferB (PureInferB act) =
    runRWST act (mempty, ScopeLevel 0) emptyPureInferState <&> (^. Lens._1)

execSTInferB :: STInferB s a -> ST s (Maybe a)
execSTInferB (STInferB act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, ScopeLevel 0, qvarGen) & runMaybeT

prettyPrint :: Pretty a => a -> IO ()
prettyPrint = print . pPrint

testCommon ::
    Pretty (Tree lang Pure) =>
    Tree Pure lang -> String -> Maybe (Tree Pure Typ) -> Maybe (Tree Pure Typ) -> IO Bool
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
            [ testA lamXYx5      "Just ((Int -> #t0) -> #t1 -> #t0)"
            , testA infinite     "Nothing"
            , testA skolem       "Nothing"
            , testA validForAll  "Just (#t0 -> #t0)"
            , testB letGen       "Just Int"
            , testB shouldNotGen "Just (#t0 -> #t0)"
            , testB record       "Just (\"a\" : Int :*: {})"
            , testB extendLit    "Nothing"
            , testB extendDup    "Nothing"
            , testB extendGood   "Just (\"b\" : Int :*: \"a\" : Int :*: {})"
            , testB unifyRows    "Just (((\"a\" : Int :*: \"b\" : Int :*: {}) -> Int -> Int) -> Int)"
            ]

