{-# LANGUAGE StandaloneDeriving, UndecidableInstances, MultiParamTypeClasses, TemplateHaskell, LambdaCase, TypeSynonymInstances, FlexibleInstances, TypeFamilies #-}

import AST
import AST.TH
import AST.Unify
import AST.Unify.IntBindingState
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.RWS
import Data.Functor.Identity
import Data.Functor.Const
import Data.Map
import Data.Maybe
import Data.IntSet

data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)

data Term v f
    = ELam v (Node f (Term v))
    | EVar v
    | EApp (Node f (Term v)) (Node f (Term v))
    | ELit Int

deriving instance (Show (f (Typ f)), Show (Row f)) => Show (Typ f)
deriving instance (Show (f (Typ f)), Show (f (Row f))) => Show (Row f)
deriving instance (Show v, Show (Node f (Term v))) => Show (Term v f)

[makeChildren, makeZipMatch] <*> [''Typ, ''Row] & sequenceA <&> concat
makeChildren ''Term -- TODO: makeZipMatch should work too

data Infer f = Infer
    { _iTyp :: f Typ
    , _iRow :: f Row
    }
Lens.makeLenses ''Infer

emptyInferState :: Infer IntBindingState
emptyInferState = Infer emptyIntBindingState emptyIntBindingState

type LamBindings v = Map String (Node (UTerm v) Typ)

type InferM = RWST (LamBindings Int) () (Infer IntBindingState) Maybe

instance OccursMonad InferM where
    type Visited InferM = Infer (Const IntSet)
    emptyVisited _ = Infer (Const mempty) (Const mempty)

instance UnifyMonad InferM Int Typ where
    binding = intBindingState iTyp
    visit _ var = (iTyp . Lens._Wrapped) (visitSet var)

instance UnifyMonad InferM Int Row where
    binding = intBindingState iRow
    visit _ var = (iRow . Lens._Wrapped) (visitSet var)

runInfer :: InferM a -> Maybe a
runInfer act = runRWST act mempty emptyInferState <&> (^. Lens._1)

infer :: Term String Identity -> InferM (Node (UTerm Int) Typ)
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

inferExpr :: Node Identity (Term String) -> Maybe (Node (UTerm Int) Typ)
inferExpr x = infer (x ^. Lens._Wrapped) >>= applyBindings & runInfer

main :: IO ()
main =
    do
        putStrLn ""
        print (inferExpr expr)
        print (inferExpr occurs)
