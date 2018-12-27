{-# LANGUAGE TemplateHaskell, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances #-}

module TypeLang where

import AST
import AST.Class.Infer
import AST.Class.Instantiate
import AST.Unify
import AST.Unify.Constraints
import AST.Unify.IntMapBinding
import AST.Term.FuncType
import AST.Term.Scheme
import AST.Term.Scope
import Control.Applicative
import qualified Control.Lens as Lens
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

data Types f = Types
    { _tTyp :: Tie f Typ
    , _tRow :: Tie f Row
    }

Lens.makePrisms ''Typ
Lens.makePrisms ''Row
Lens.makeLenses ''Types
makeChildrenAndZipMatch [''Typ, ''Row, ''Types]

deriving instance SubTreeConstraint Typ f Show => Show (Typ f)
deriving instance SubTreeConstraint Row f Show => Show (Row f)

instance HasChild Types Typ where getChild = tTyp
instance HasChild Types Row where getChild = tRow

type instance TypeConstraintsOf Typ = QuantificationScope
type instance TypeConstraintsOf Row = QuantificationScope

type IntInferState = (Tree Types IntBindingState, Tree Types (Const Int))

emptyIntInferState :: IntInferState
emptyIntInferState =
    ( Types emptyIntBindingState emptyIntBindingState
    , Types (Const 0) (Const 0)
    )

type STInferState s = Tree Types (Const (STRef s Int))

type instance SchemeType (Tree Pure Typ) = Typ
instance (MonadInfer m, Recursive (Unify m) Typ) => Instantiate m (Tree Pure Typ)

instance HasQuantifiedVar Typ where
    type QVar Typ = String
    quantifiedVar = _TVar

instance HasQuantifiedVar Row where
    type QVar Row = String
    quantifiedVar = _RVar

instance HasFuncType Typ where
    funcType = _TFun

instance HasScopeTypes v Typ a => HasScopeTypes v Typ (a, x) where
    scopeTypes = Lens._1 . scopeTypes

instance HasScopeTypes v Typ a => HasScopeTypes v Typ (a, x, y) where
    scopeTypes = Lens._1 . scopeTypes
