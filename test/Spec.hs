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
import           Text.PrettyPrint (($+$))
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
    Pure . ALam . scope $ \x ->
    TVar "a" & Pure
    & Scheme (Types (Vars ["a"]) (Vars [])) & Pure
    & TypeSig (var x) & ATypeSig & Pure

validForAll :: Tree Pure (LangA EmptyScope)
validForAll =
    -- (\x -> x) :: forall a. a
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

execIntInferA :: IntInferA a -> Maybe a
execIntInferA (IntInferA act) =
    runRWST act (mempty, ScopeLevel 0) emptyIntInferState <&> (^. Lens._1)

execSTInferA :: STInferA s a -> ST s (Maybe a)
execSTInferA (STInferA act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, ScopeLevel 0, qvarGen) & runMaybeT

execIntInferB :: IntInferB a -> Maybe a
execIntInferB (IntInferB act) =
    runRWST act (mempty, ScopeLevel 0) emptyIntInferState <&> (^. Lens._1)

execSTInferB :: STInferB s a -> ST s (Maybe a)
execSTInferB (STInferB act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, ScopeLevel 0, qvarGen) & runMaybeT

prettyPrint :: Pretty a => a -> IO ()
prettyPrint = print . pPrint

testPrelude :: Pretty (Tree lang Pure) => Tree Pure lang -> IO ()
testPrelude expr =
    do
        putStrLn ""
        pPrint expr $+$ Pretty.text "inferred to:" & print

testA :: Tree Pure (LangA EmptyScope) -> IO ()
testA expr =
    do
        testPrelude expr
        execIntInferA (inferExpr expr) & prettyPrint
        runST (execSTInferA (inferExpr expr)) & prettyPrint

testB :: Tree Pure LangB -> IO ()
testB expr =
    do
        testPrelude expr
        execIntInferB (inferExpr expr) & prettyPrint
        runST (execSTInferB (inferExpr expr)) & prettyPrint

main :: IO ()
main =
    do
        testA lamXYx5
        testA infinite
        testA skolem
        testA validForAll
        testB letGen
        testB shouldNotGen
        testB record
        testB extendLit
        testB extendDup
        testB extendGood
        testB unifyRows
