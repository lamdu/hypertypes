{-# LANGUAGE FlexibleContexts #-}

import LangA
import TypeLang

import AST
import AST.Class.Infer
import AST.Class.Recursive
import AST.Term.Apply
import AST.Term.FuncType
import AST.Term.Scheme
import AST.Term.Scope
import AST.Term.TypeSig
import AST.Unify
import AST.Unify.STBinding
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
    & ATypeSig
    & Pure

inferExpr ::
    (DeBruijnIndex k, TermInfer1Deps env m) =>
    Tree Pure (LangA k) ->
    m (Tree Pure Typ)
inferExpr x =
    inferNode (wrap (Proxy :: Proxy Children) (Ann ()) x)
    <&> (^. nodeType)
    >>= applyBindings

runIntInfer :: IntInfer (ScopeTypes (Const Int) Typ) () a -> Maybe a
runIntInfer act = runRWST act (mempty, InferLevel 0) emptyIntInferState <&> (^. Lens._1)

runSTInfer :: STInfer (ScopeTypes (STVar s) Typ) s a -> ST s (Maybe a)
runSTInfer act =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, InferLevel 0, qvarGen) & runMaybeT

main :: IO ()
main =
    do
        putStrLn ""
        print (runIntInfer (inferExpr expr))
        print (runST (runSTInfer (inferExpr expr)))
        putStrLn ""
        print (runIntInfer (inferExpr infinite))
        print (runST (runSTInfer (inferExpr infinite)))
        putStrLn ""
        print (runIntInfer (inferExpr skolem))
        print (runST (runSTInfer (inferExpr skolem)))
        putStrLn ""
        print (runIntInfer (inferExpr validForAll))
        print (runST (runSTInfer (inferExpr validForAll)))
