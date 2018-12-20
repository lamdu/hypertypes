{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, DataKinds #-}

module TypeLang where

import AST
import AST.Unify
import AST.Unify.IntMapBinding
import AST.Unify.STBinding
import AST.Term.FuncType
import AST.Term.Scope
import Control.Lens (ALens')
import qualified Control.Lens as Lens
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.ST.Class (MonadST(..))
import Control.Monad.Trans.Maybe
import Data.Functor.Const
import Data.STRef

data Typ f
    = TInt
    | TFun (FuncType Typ f)
    | TRow (Row f)
    | TVar String

data Row f
    = REmpty
    | RExtend String (Tie f Typ) (Tie f Row)
    | RVar String

Lens.makePrisms ''Typ
Lens.makePrisms ''Row
makeChildrenAndZipMatch [''Typ, ''Row]

deriving instance SubTreeConstraint Typ f Show => Show (Typ f)
deriving instance SubTreeConstraint Row f Show => Show (Row f)

data InferState f = InferState
    { _iTyp :: f Typ
    , _iRow :: f Row
    }
Lens.makeLenses ''InferState

type IntInferState = (InferState IntBindingState, InferState (Const Int))

emptyIntInferState :: IntInferState
emptyIntInferState =
    ( InferState emptyIntBindingState emptyIntBindingState
    , InferState (Const 0) (Const 0)
    )

instance HasQuantifiedVar Typ where
    type QVar Typ = Int
    -- We force quantified variables to int
    quantifiedVar = TVar . ('t':) . show

instance HasQuantifiedVar Row where
    type QVar Row = Int
    -- We force quantified variables to empty rows
    quantifiedVar = RVar . ('r':) . show

type IntInfer r w = RWST r w IntInferState Maybe

type instance UniVar (IntInfer r w) = Const Int

instance Monoid w => Unify (IntInfer r w) Typ where
    binding = intBindingState (Lens._1 . iTyp)
    newQuantifiedVariable _ = increase (Lens._2 . iTyp . Lens._Wrapped)

instance Monoid w => Unify (IntInfer r w) Row where
    binding = intBindingState (Lens._1 . iRow)
    newQuantifiedVariable _ = increase (Lens._2 . iRow . Lens._Wrapped)

instance Monoid w => Recursive (Unify (IntInfer r w)) Typ
instance Monoid w => Recursive (Unify (IntInfer r w)) Row

type STInferState s = InferState (Const (STRef s Int))

type STInfer r s = ReaderT (r, STInferState s) (MaybeT (ST s))

type instance UniVar (STInfer r s) = STVar s

readModifySTRef :: STRef s a -> (a -> a) -> ST s (a, a)
readModifySTRef ref func =
    do
        old <- readSTRef ref
        let new = func old
        (old, new) <$ (new `seq` writeSTRef ref new)

newStQuantified ::
    (MonadReader (a, STInferState s) m, MonadST m) =>
    ALens' (STInferState s) (Const (STRef (World m) Int) (ast :: Knot -> *)) -> m Int
newStQuantified l =
    Lens.view (Lens._2 . Lens.cloneLens l . Lens._Wrapped)
    >>= liftST . fmap fst . (`readModifySTRef` (+1))

instance Unify (STInfer r s) Typ where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified iTyp

instance Unify (STInfer r s) Row where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified iRow

instance Recursive (Unify (STInfer r s)) Typ
instance Recursive (Unify (STInfer r s)) Row

instance HasFuncType Typ where
    funcType = _TFun

instance HasScopeTypes v Typ a => HasScopeTypes v Typ (a, x) where
    scopeTypes = Lens._1 . scopeTypes
