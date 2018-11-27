{-# LANGUAGE StandaloneDeriving, UndecidableInstances, MultiParamTypeClasses, TemplateHaskell, LambdaCase, TypeSynonymInstances, FlexibleInstances, TypeFamilies #-}

import AST
import AST.Unify
import AST.Unify.IntBindingState
import AST.ZipMatch
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.RWS
import Control.Monad.Error.Class
import Data.Functor.Identity
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

instance Children Typ where
    type ChildrenConstraint Typ constraint = (constraint Typ, constraint Row)
    children _ _ TInt = pure TInt
    children _ f (TFun x y) = TFun <$> f x <*> f y
    children p f (TRow x) = TRow <$> children p f x

instance Children Row where
    type ChildrenConstraint Row constraint = (constraint Typ, constraint Row)
    children _ _ REmpty = pure REmpty
    children _ f (RExtend k x y) = RExtend k <$> f x <*> f y

instance ZipMatch Typ where
    zipMatch _ _ TInt TInt = pure TInt
    zipMatch _ f (TFun a0 r0) (TFun a1 r1) = TFun <$> f a0 a1 <*> f r0 r1
    zipMatch p f (TRow r0) (TRow r1) = zipMatch p f r0 r1 <&> TRow
    zipMatch _ _ _ _ = throwError ()

instance ZipMatch Row where
    zipMatch _ _ REmpty REmpty = pure REmpty
    zipMatch _ f (RExtend k0 v0 r0) (RExtend k1 v1 r1)
        | k0 == k1 = RExtend k0 <$> f v0 v1 <*> f r0 r1
    zipMatch _ _ _ _ = throwError ()

data InferState = InferState
    { _typBindings :: IntBindingState Typ
    , _rowBindings :: IntBindingState Row
    }
Lens.makeLenses ''InferState

emptyInferState :: InferState
emptyInferState = InferState emptyIntBindingState emptyIntBindingState

type InferM = RWST (Map String (Node (UTerm Int) Typ)) () InferState Maybe

instance UnifyMonad InferM Int Typ where
    binding = intBindingState typBindings

instance UnifyMonad InferM Int Row where
    binding = intBindingState rowBindings

runInfer :: InferM a -> Maybe a
runInfer act = runRWST act mempty emptyInferState <&> (^. Lens._1)

infer :: Term Identity -> InferM (Node (UTerm Int) Typ)
infer ELit{} = UTerm TInt & pure
infer (EVar var) = Lens.view (Lens.at var) <&> fromMaybe (error "name error")
infer (ELam var (Identity body)) =
    do
        varType <- newVar binding
        local (Lens.at var ?~ varType) (infer body) <&> TFun varType <&> UTerm
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

expr :: Node Identity Term
expr =
    -- \x -> x 5
    ELit 5 & Identity
    & EApp (EVar "x" & Identity) & Identity
    & ELam "x" & Identity

typ :: Node (UTerm Int) Typ
typ = runInfer (infer (expr ^. Lens._Wrapped) >>= applyBindings) & fromMaybe (error "infer failed!")

main :: IO ()
main =
    do
        putStrLn ""
        print typ
