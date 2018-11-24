{-# LANGUAGE StandaloneDeriving, UndecidableInstances, MultiParamTypeClasses, TemplateHaskell, LambdaCase, TypeSynonymInstances, FlexibleInstances #-}

import AST
import AST.Ann
import AST.Infer
import AST.Unify
import AST.Unify.IntBindingState
import Control.Lens
import Control.Monad.RWS
import Control.Monad.Error.Class
import Data.IntMap
import Data.Map
import Data.Maybe

data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)

data Term f
    = ELam String (Node f Term)
    | EVar String
    | EApp (Node f Term) (Node f Term)
    | ELit Int

deriving instance (Show (f (Typ f)), Show (Row f)) => Show (Typ f)
deriving instance (Show (f (Typ f)), Show (f (Row f))) => Show (Row f)
deriving instance Show (Node f Term) => Show (Term f)

data InferState = InferState
    { _typBindings :: IntBindingState Typ
    , _rowBindings :: IntBindingState Row
    }
makeLenses ''InferState

type InferM = RWST (Map String (Node (UTerm Int) Typ)) () InferState Maybe

typ :: Node Identity Typ
typ =
    Identity REmpty
    & RExtend "hello" (Identity TInt) & TRow & Identity
    & TFun (Identity TInt) & Identity

instance UnifyMonad Int Typ InferM where
    binding = intBindingState typBindings
    unifyBody TInt TInt = pure TInt
    unifyBody (TFun a0 r0) (TFun a1 r1) = TFun <$> unify a0 a1 <*> unify r0 r1
    unifyBody (TRow r0) (TRow r1) = TRow <$> unifyBody r0 r1
    unifyBody _ _ = throwError ()

instance UnifyMonad Int Row InferM where
    binding = intBindingState rowBindings
    unifyBody REmpty REmpty = pure REmpty
    unifyBody (RExtend k0 v0 r0) (RExtend k1 v1 r1)
        | k0 == k1 = RExtend k0 <$> unify v0 v1 <*> unify r0 r1
    unifyBody _ _ = throwError ()

instance InferMonad Term Int Typ InferM where
    inferBody ELit{} = UTerm TInt & pure
    inferBody (EVar var) = view (at var) <&> fromMaybe (error "name error")
    inferBody (ELam var body) =
        do
            varType <- newVar binding
            local (at var ?~ varType) (inferBody (body ^. val)) <&> TFun varType <&> UTerm
    inferBody (EApp func arg) =
        do
            argType <- inferBody (arg ^. val)
            inferBody (func ^. val)
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

main :: IO ()
main =
    do
        putStrLn ""
        print typ
