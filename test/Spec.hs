{-# LANGUAGE LambdaCase, FlexibleContexts, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

import TermLang
import TypeLang

import AST
import AST.Unify
import AST.Unify.STBinding
import Control.Lens (Lens')
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.ST
import Data.Functor.Const
import Data.Functor.Identity
import Data.Map
import Data.Maybe

type LamBindings v = Map String (Node (UTerm v) Typ)

class HasLamBindings v env where
    lamBindings :: Lens' env (LamBindings v)

instance HasLamBindings v (LamBindings v) where
    lamBindings = id

instance HasLamBindings v a => HasLamBindings v (a, x) where
    lamBindings = Lens._1 . lamBindings

infer ::
    (MonadReader env m, HasLamBindings (Var m) env, UnifyMonad m Typ) =>
    Term String Identity -> m (UNode m Typ)
infer ELit{} = UTerm TInt & pure
infer (EVar var) = Lens.view (Lens.cloneLens lamBindings . Lens.at var) <&> fromMaybe (error "name error")
infer (ELam var (Identity body)) =
    do
        varType <- newVar binding
        local (lamBindings . Lens.at var ?~ varType) (infer body) <&> TFun varType <&> UTerm
infer (EApp (Identity func) (Identity arg)) =
    do
        argType <- infer arg
        infer func
            >>=
            \case
            UTerm (TFun funcArg funcRes) ->
                -- Func already inferred to be function,
                -- skip creating new variable for result for faster inference.
                funcRes <$ unify funcArg argType
            x ->
                do
                    funcRes <- newVar binding
                    funcRes <$ unify x (UTerm (TFun argType funcRes))

expr :: Node Identity (Term String)
expr =
    -- \x -> x 5
    ELit 5 & Identity
    & EApp (EVar "x" & Identity) & Identity
    & ELam "x" & Identity

occurs :: Node Identity (Term String)
occurs =
    -- \x -> x x
    EApp x x & Identity
    & ELam "x" & Identity
    where
        x = EVar "x" & Identity

inferExpr ::
    (MonadReader env m, HasLamBindings (Var m) env, UnifyMonad m Typ) =>
    Node Identity (Term String) -> m (Node (UTerm (Var m)) Typ)
inferExpr x = infer (x ^. Lens._Wrapped) >>= applyBindings

runIntInfer :: IntInfer (LamBindings (Const Int)) () a -> Maybe a
runIntInfer act = runRWST act mempty emptyIntInferState <&> (^. Lens._1)

runSTInfer :: STInfer (LamBindings (STVar s)) s a -> ST s (Either () ())
runSTInfer act =
    newSTInferState <&> (,) mempty
    >>= runExceptT . runReaderT act
    <&> Lens._Right .~ ()

main :: IO ()
main =
    do
        putStrLn ""
        print (runIntInfer (inferExpr expr))
        print (runST (runSTInfer (inferExpr expr)))
        print (runIntInfer (inferExpr occurs))
        print (runST (runSTInfer (inferExpr occurs)))
