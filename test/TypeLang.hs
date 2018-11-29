{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}

module TypeLang where

import AST
import AST.Unify
import AST.Unify.IntBindingState
import AST.TH
import qualified Control.Lens as Lens
import Control.Monad.RWS
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

data Infer f = Infer
    { _iTyp :: f Typ
    , _iRow :: f Row
    }
Lens.makeLenses ''Infer

emptyInferState :: Infer IntBindingState
emptyInferState = Infer emptyIntBindingState emptyIntBindingState

type instance Var (RWST r w (Infer IntBindingState) Maybe) = Const Int

instance Monoid w => OccursMonad (RWST r w (Infer IntBindingState) Maybe) where
    type Visited (RWST r w (Infer IntBindingState) Maybe) = Infer (Const IntSet)
    emptyVisited _ = Infer (Const mempty) (Const mempty)

instance Monoid w => UnifyMonad (RWST r w (Infer IntBindingState) Maybe) Typ where
    binding = intBindingState iTyp
    visit (Const var) = (iTyp . Lens._Wrapped) (visitSet var)

instance Monoid w => UnifyMonad (RWST r w (Infer IntBindingState) Maybe) Row where
    binding = intBindingState iRow
    visit (Const var) = (iRow . Lens._Wrapped) (visitSet var)
