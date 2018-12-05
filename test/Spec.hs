{-# LANGUAGE FlexibleContexts #-}

import TermLang
import TypeLang

import AST
import AST.Apply
import AST.Infer
import AST.Scope
import AST.Unify
import AST.Unify.STBinding
import AST.UTerm
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.ST
import Control.Monad.Trans.Maybe
import Data.Functor.Const
import Data.Functor.Identity

expr :: Node Identity (Term EmptyScope)
expr =
    -- \x -> x 5
    ELit 5 & Identity
    & Apply (EVar (ScopeVar Nothing) & Identity) & EApp & Identity
    & Scope & ELam & Identity

occurs :: Node Identity (Term EmptyScope)
occurs =
    -- \x -> x x
    Apply x x & EApp & Identity
    & Scope & ELam & Identity
    where
        x = ScopeVar Nothing & EVar & Identity

inferExpr ::
    (DeBruijnIndex k, MonadReader env m, HasVarTypes (Var m) Typ env, UnifyMonad m Typ) =>
    Node Identity (Term k) -> m (Node (UTerm (Var m)) Typ)
inferExpr x = infer (x ^. Lens._Wrapped) >>= applyBindings

runIntInfer :: IntInfer (VarTypes (Const Int) Typ) () a -> Maybe a
runIntInfer act = runRWST act mempty emptyIntInferState <&> (^. Lens._1)

runSTInfer :: STInfer (VarTypes (STVar s) Typ) s a -> ST s (Maybe a)
runSTInfer act =
    newSTInferState <&> (,) mempty
    >>= runMaybeT . runReaderT act

main :: IO ()
main =
    do
        putStrLn ""
        print (runIntInfer (inferExpr expr))
        print (runST (runSTInfer (inferExpr expr <&> stBindingToInt)))
        print (runIntInfer (inferExpr occurs))
        print (runST (runSTInfer (inferExpr occurs <&> stBindingToInt)))
