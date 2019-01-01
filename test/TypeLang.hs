{-# LANGUAGE TemplateHaskell, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances #-}

module TypeLang where

import Algebra.Lattice
import Algebra.PartialOrd
import AST
import AST.Class.Instantiate
import AST.Unify
import AST.Unify.Constraints
import AST.Unify.IntMapBinding
import AST.Term.FuncType
import AST.Term.RowExtend
import AST.Term.Scheme
import AST.Term.Scope
import Control.Applicative
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Data.Set
import Data.STRef

data Typ f
    = TInt
    | TFun (FuncType Typ f)
    | TRec (Tie f Row)
    | TVar String

data Row f
    = REmpty
    | RExtend (RowExtend String Typ Row f)
    | RVar String

data RowConstraints = RowConstraints
    { _rForbiddenFields :: Set String
    , _rScope :: QuantificationScope
    } deriving (Eq, Show)

data Types f = Types
    { _tTyp :: Tie f Typ
    , _tRow :: Tie f Row
    }

Lens.makePrisms ''Typ
Lens.makePrisms ''Row
Lens.makeLenses ''RowConstraints
Lens.makeLenses ''Types
makeChildrenAndZipMatch [''Typ, ''Row, ''Types]

deriving instance SubTreeConstraint Typ f Show => Show (Typ f)
deriving instance SubTreeConstraint Row f Show => Show (Row f)

instance HasChild Types Typ where getChild = tTyp
instance HasChild Types Row where getChild = tRow

instance PartialOrd RowConstraints where
    RowConstraints f0 s0 `leq` RowConstraints f1 s1 = f0 `leq` f1 && s0 `leq` s1

instance JoinSemiLattice RowConstraints where
    RowConstraints f0 s0 \/ RowConstraints f1 s1 = RowConstraints (f0 \/ f1) (s0 \/ s1)

instance TypeConstraints RowConstraints where
    constraintsFromScope = RowConstraints mempty
    constraintsScope = rScope

instance HasTypeConstraints Typ
instance HasTypeConstraints Row where
    type TypeConstraintsOf Row = RowConstraints
    propagateConstraints _ _ _ _ REmpty = pure REmpty
    propagateConstraints _ _ _ _ (RVar x) = RVar x & pure
    propagateConstraints p c e u (RExtend x) =
        propagateRowConstraints p rForbiddenFields c (e . (`RowConstraints` mempty) . singleton) u RExtend x

type IntInferState = (Tree Types IntBindingState, Tree Types (Const Int))

emptyIntInferState :: IntInferState
emptyIntInferState =
    ( Types emptyIntBindingState emptyIntBindingState
    , Types (Const 0) (Const 0)
    )

type STInferState s = Tree Types (Const (STRef s Int))

type instance SchemeType (Tree Pure Typ) = Typ
instance Recursive (Unify m) Typ => Instantiate m (Tree Pure Typ)

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
