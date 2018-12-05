{-# LANGUAGE LambdaCase, FlexibleContexts, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}

import TermLang
import TypeLang

import AST
import AST.Scope
import AST.Unify
import AST.Unify.STBinding
import AST.UTerm
import Control.Lens (Lens')
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.ST
import Control.Monad.Trans.Maybe
import Data.Functor.Const
import Data.Functor.Identity
import Data.IntMap
import Data.Maybe
import Data.Proxy

type LamBindings v = IntMap (Node (UTerm v) Typ)

class HasLamBindings v env where
    lamBindings :: Lens' env (LamBindings v)

instance HasLamBindings v (LamBindings v) where
    lamBindings = id

instance HasLamBindings v a => HasLamBindings v (a, x) where
    lamBindings = Lens._1 . lamBindings

infer ::
    forall k env m.
    (DeBruijnIndex k, MonadReader env m, HasLamBindings (Var m) env, UnifyMonad m Typ) =>
    Term k Identity -> m (UNode m Typ)
infer ELit{} = UTerm TInt & pure
infer (EVar var) =
    Lens.view (Lens.cloneLens lamBindings . Lens.at (inverseDeBruijnIndex var)) <&> fromMaybe (error "name error")
infer (ELam (Scope (Identity body))) =
    do
        varType <- newVar binding
        local (lamBindings . Lens.at (deBruijnIndexMax (Proxy :: Proxy (Maybe k))) ?~ varType) (infer body) <&> TFun varType <&> UTerm
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

expr :: Node Identity (Term EmptyScope)
expr =
    -- \x -> x 5
    ELit 5 & Identity
    & EApp (EVar Nothing & Identity) & Identity
    & Scope & ELam & Identity

occurs :: Node Identity (Term EmptyScope)
occurs =
    -- \x -> x x
    EApp x x & Identity
    & Scope & ELam & Identity
    where
        x = EVar Nothing & Identity

inferExpr ::
    (DeBruijnIndex k, MonadReader env m, HasLamBindings (Var m) env, UnifyMonad m Typ) =>
    Node Identity (Term k) -> m (Node (UTerm (Var m)) Typ)
inferExpr x = infer (x ^. Lens._Wrapped) >>= applyBindings

runIntInfer :: IntInfer (LamBindings (Const Int)) () a -> Maybe a
runIntInfer act = runRWST act mempty emptyIntInferState <&> (^. Lens._1)

runSTInfer :: STInfer (LamBindings (STVar s)) s a -> ST s (Maybe a)
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
