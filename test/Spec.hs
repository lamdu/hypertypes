{-# LANGUAGE FlexibleContexts #-}

import TermLang
import TypeLang

import AST
import AST.Functor.UTerm
import AST.Infer
import AST.Term.Apply
import AST.Term.Scope
import AST.Unify
import AST.Unify.STBinding
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.ST
import Control.Monad.Trans.Maybe
import Data.Functor.Const
import Data.Functor.Identity

var :: DeBruijnIndex k => Int -> Identity (Term k f)
var = Identity . EVar . scopeVar

expr :: Node Identity (Term EmptyScope)
expr =
    -- \x y -> x 5
    Identity . ELam . scope $ \x ->
    Identity . ELam . scope $ \_y ->
    ELit 5 & Identity
    & Apply (var x) & EApp & Identity

occurs :: Node Identity (Term EmptyScope)
occurs =
    -- \x -> x x
    Identity . ELam . scope $ \x ->
    Apply (var x) (var x) & EApp & Identity

inferExpr ::
    (DeBruijnIndex k, MonadReader env m, HasScopeTypes (Var m) Typ env, Unify m Typ) =>
    Node Identity (Term k) ->
    m (Node (UTerm (Var m)) Typ)
inferExpr x =
    inferNode (hoistNode (Ann () . runIdentity) x)
    <&> (^. nodeType)
    >>= applyBindings

runIntInfer :: IntInfer (ScopeTypes (Const Int) Typ) () a -> Maybe a
runIntInfer act = runRWST act mempty emptyIntInferState <&> (^. Lens._1)

runSTInfer :: STInfer (ScopeTypes (STVar s) Typ) s a -> ST s (Maybe a)
runSTInfer act =
    newSTInferState <&> (,) mempty
    >>= runMaybeT . runReaderT act

main :: IO ()
main =
    do
        putStrLn ""
        print (runIntInfer (inferExpr expr))
        print (runST (runSTInfer (inferExpr expr <&> stBindingToInt)))
        putStrLn ""
        print (runIntInfer (inferExpr occurs))
        print (runST (runSTInfer (inferExpr occurs <&> stBindingToInt)))
