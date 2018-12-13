{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}

module TypeLang where

import AST
import AST.Class.Infer
import AST.Unify
import AST.Unify.IntMapBinding
import AST.Unify.STBinding
import AST.Term.Scope
import qualified Control.Lens as Lens
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.Trans.Maybe
import Data.Functor.Const

data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)

deriving instance IfChildNodes Typ f Show => Show (Typ f)
deriving instance IfChildNodes Row f Show => Show (Row f)

Lens.makePrisms ''Typ
Lens.makePrisms ''Row
makeChildrenAndZipMatch [''Typ, ''Row]

data InferState f = InferState
    { _iTyp :: f Typ
    , _iRow :: f Row
    }
Lens.makeLenses ''InferState

emptyIntInferState :: InferState IntBindingState
emptyIntInferState = InferState emptyIntBindingState emptyIntBindingState

instance HasQuantifiedVar Typ where
    type QVar Typ = ()
    -- We force quantified variables to int
    quantifiedVar _ = TInt

instance HasQuantifiedVar Row where
    type QVar Row = ()
    -- We force quantified variables to empty rows
    quantifiedVar _ = REmpty

type IntInfer r w = RWST r w (InferState IntBindingState) Maybe

type instance UniVar (IntInfer r w) = Const Int

instance Monoid w => Unify (IntInfer r w) Typ where
    binding = intBindingState iTyp

instance Monoid w => Unify (IntInfer r w) Row where
    binding = intBindingState iRow

instance Monoid w => Recursive (Unify (IntInfer r w)) Typ
instance Monoid w => Recursive (Unify (IntInfer r w)) Row

type STInfer r s = ReaderT r (MaybeT (ST s))

type instance UniVar (STInfer r s) = STVar s

instance Unify (STInfer r s) Typ where
    binding = stBindingState

instance Unify (STInfer r s) Row where
    binding = stBindingState

instance Recursive (Unify (STInfer r s)) Typ
instance Recursive (Unify (STInfer r s)) Row

instance FuncType Typ where
    funcType = _TFun

instance HasScopeTypes v Typ a => HasScopeTypes v Typ (a, x) where
    scopeTypes = Lens._1 . scopeTypes
