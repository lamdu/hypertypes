{-# LANGUAGE FlexibleContexts #-}

import LangA
import LangB
import TypeLang

import AST
import AST.Class.Infer
import AST.Class.Recursive
import AST.Term.Apply
import AST.Term.FuncType
import AST.Term.Lam
import AST.Term.Let
import AST.Term.Scheme
import AST.Term.Scope
import AST.Term.TypeSig
import AST.Term.Var
import AST.Unify
import AST.Unify.Term
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.ST
import Control.Monad.Trans.Maybe
import Data.Functor.Const
import Data.Proxy
import Data.STRef

var :: DeBruijnIndex k => Int -> Tree Pure (LangA k)
var = Pure . AVar . scopeVar

uniType :: Tree Pure Typ -> Tree Pure (Scheme Types Typ)
uniType typ =
    Pure Scheme
    { _sForAlls = Types (Vars []) (Vars [])
    , _sTyp = typ
    }

expr :: Tree Pure (LangA EmptyScope)
expr =
    -- \x y -> x (5 :: Int)
    Pure . ALam . scope $ \x ->
    Pure . ALam . scope $ \_y ->
    ALit 5 & Pure
    & TypeSig (uniType (Pure TInt)) & ATypeSig & Pure
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
    var x
    & TypeSig (Pure
        (Scheme
            (Types (Vars ["a"]) (Vars []))
            (Pure (TVar "a"))
        )) & ATypeSig & Pure

validForAll :: Tree Pure (LangA EmptyScope)
validForAll =
    -- (\x -> x) :: forall a. a
    scope var & ALam & Pure
    & TypeSig
        (Pure (Scheme
            (Types (Vars ["a"]) (Vars []))
            (Pure (TFun (FuncType (Pure (TVar "a")) (Pure (TVar "a")))))
        ))
    & ATypeSig & Pure

letGen :: Tree Pure LangB
letGen =
    BLit 5 & Pure
    & Apply (Pure (BApp (Apply i i))) & BApp & Pure
    & Let "id" (Pure (BLam (Lam "x" (Pure (BVar (Var "x"))))))
    & BLet & Pure
    where
        i = Var "id" & BVar & Pure

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
    runRWST act (mempty, InferLevel 0) emptyIntInferState <&> (^. Lens._1)

execSTInferA :: STInferA s a -> ST s (Maybe a)
execSTInferA (STInferA act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, InferLevel 0, qvarGen) & runMaybeT

execIntInferB :: IntInferB String a -> Maybe a
execIntInferB (IntInferB act) =
    runRWST act (mempty, InferLevel 0) emptyIntInferState <&> (^. Lens._1)

execSTInferB :: STInferB String s a -> ST s (Maybe a)
execSTInferB (STInferB act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, InferLevel 0, qvarGen) & runMaybeT

main :: IO ()
main =
    do
        putStrLn ""
        print (execIntInferA (inferExpr expr))
        print (runST (execSTInferA (inferExpr expr)))
        putStrLn ""
        print (execIntInferA (inferExpr infinite))
        print (runST (execSTInferA (inferExpr infinite)))
        putStrLn ""
        print (execIntInferA (inferExpr skolem))
        print (runST (execSTInferA (inferExpr skolem)))
        putStrLn ""
        print (execIntInferA (inferExpr validForAll))
        print (runST (execSTInferA (inferExpr validForAll)))
        putStrLn ""
        print (execIntInferB (inferExpr letGen))
        print (runST (execSTInferB (inferExpr letGen)))
