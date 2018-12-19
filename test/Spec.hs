{-# LANGUAGE FlexibleContexts #-}

import TermLang
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

var :: DeBruijnIndex k => Int -> Tree Pure (Term k)
var = Pure . EVar . scopeVar

uniType :: Tree Pure Typ -> Tree Pure (Scheme Types Typ)
uniType typ =
    Pure Scheme
    { _sForAlls = Types (Vars []) (Vars [])
    , _sTyp = typ
    }

expr :: Tree Pure (Term EmptyScope)
expr =
    -- \x y -> x (5 :: Int)
    Pure . ELam . scope $ \x ->
    Pure . ELam . scope $ \_y ->
    ELit 5 & Pure
    & TypeSig (uniType (Pure TInt)) & ETypeSig & Pure
    & Apply (var x) & EApp & Pure

infinite :: Tree Pure (Term EmptyScope)
infinite =
    -- \x -> x x
    Pure . ELam . scope $ \x ->
    Apply (var x) (var x) & EApp & Pure

skolem :: Tree Pure (Term EmptyScope)
skolem =
    -- \x -> (x :: forall a. a)
    Pure . ELam . scope $ \x ->
    var x
    & TypeSig (Pure
        (Scheme
            (Types (Vars ["a"]) (Vars []))
            (Pure (TVar "a"))
        )) & ETypeSig & Pure

validForAll :: Tree Pure (Term EmptyScope)
validForAll =
    -- (\x -> x) :: forall a. a
    scope var & ELam & Pure
    & TypeSig
        (Pure (Scheme
            (Types (Vars ["a"]) (Vars []))
            (Pure (TFun (FuncType (Pure (TVar "a")) (Pure (TVar "a")))))
        ))
    & ETypeSig
    & Pure

inferExpr ::
    (DeBruijnIndex k, TermInfer1Deps env m) =>
    Tree Pure (Term k) ->
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
