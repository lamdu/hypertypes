{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}

module TypeLang where

import AST
import AST.Recursive
import AST.Unify
import AST.Unify.IntMapBinding
import AST.Unify.STBinding
import AST.TH
import qualified Control.Lens as Lens
import Control.Monad.Except
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.ST.Class (MonadST(..))
import Data.Functor.Const
import Data.IntSet

data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)

deriving instance (Show (f (Typ f)), Show (Row f)) => Show (Typ f)
deriving instance (Show (f (Typ f)), Show (f (Row f))) => Show (Row f)

concat <$> sequenceA ([makeChildren, makeZipMatch] <*> [''Typ, ''Row])
instance Recursive Typ
instance Recursive Row

data Infer f = Infer
    { _iTyp :: f Typ
    , _iRow :: f Row
    }
Lens.makeLenses ''Infer

emptyIntInferState :: Infer IntBindingState
emptyIntInferState = Infer emptyIntBindingState emptyIntBindingState

newSTInferState :: MonadST m => m (Infer (STBindingState (World m)))
newSTInferState = Infer <$> newSTBindingState <*> newSTBindingState

emptyInferVisited :: Infer (Const IntSet)
emptyInferVisited = Infer (Const mempty) (Const mempty)

type IntInfer r w = RWST r w (Infer IntBindingState) Maybe

type instance Var (IntInfer r w) = Const Int

instance Monoid w => OccursMonad (IntInfer r w) where
    type Visited (IntInfer r w) = Infer (Const IntSet)
    emptyVisited _ = emptyInferVisited

instance Monoid w => UnifyMonad (IntInfer r w) Typ where
    binding = intBindingState iTyp
    visit = iTyp . Lens._Wrapped . intVisit

instance Monoid w => UnifyMonad (IntInfer r w) Row where
    binding = intBindingState iRow
    visit = iRow . Lens._Wrapped . intVisit

type STInfer r s = ReaderT (r, Infer (STBindingState s)) (ExceptT () (ST s))

type instance Var (STInfer r s) = STVar s

instance OccursMonad (STInfer r s) where
    type Visited (STInfer r s) = Infer (Const IntSet)
    emptyVisited _ = emptyInferVisited

instance UnifyMonad (STInfer r s) Typ where
    binding = stBindingState (Lens.view (Lens._2 . iTyp))
    visit = iTyp . Lens._Wrapped . stVisit

instance UnifyMonad (STInfer r s) Row where
    binding = stBindingState (Lens.view (Lens._2 . iRow))
    visit = iRow . Lens._Wrapped . stVisit
