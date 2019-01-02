{-# LANGUAGE MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, FlexibleInstances, FlexibleContexts #-}

module TypeLang where

import           AST
import           AST.Class.Infer.ScopeLevel
import           AST.Class.Instantiate
import           AST.Term.FuncType
import           AST.Term.RowExtend
import           AST.Term.Scheme
import           AST.Term.Scope
import           AST.Unify
import           AST.Unify.Constraints
import           AST.Unify.PureBinding
import           AST.Unify.Term
import           Algebra.Lattice
import           Algebra.PartialOrd
import           Control.Applicative
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.STRef
import           Data.Set (Set, singleton)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

newtype Name = Name String deriving (Eq, Ord, Show)

data Typ k
    = TInt
    | TFun (FuncType Typ k)
    | TRec (Tie k Row)
    | TVar Name

data Row k
    = REmpty
    | RExtend (RowExtend Name Typ Row k)
    | RVar Name

data RConstraints = RowConstraints
    { _rForbiddenFields :: Set Name
    , _rScope :: ScopeLevel
    } deriving (Eq, Show)

data Types k = Types
    { _tTyp :: Tie k Typ
    , _tRow :: Tie k Row
    }

Lens.makePrisms ''Typ
Lens.makePrisms ''Row
Lens.makeLenses ''RConstraints
Lens.makeLenses ''Types
makeChildrenAndZipMatch [''Typ, ''Row, ''Types]

deriving instance SubTreeConstraint Typ k Eq   => Eq   (Typ k)
deriving instance SubTreeConstraint Row k Eq   => Eq   (Row k)
deriving instance SubTreeConstraint Typ k Show => Show (Typ k)
deriving instance SubTreeConstraint Row k Show => Show (Row k)

instance Pretty Name where
    pPrint (Name x) = Pretty.text x

instance SubTreeConstraint Types k Pretty => Pretty (Types k) where
    pPrintPrec lvl p (Types typ row) =
        pPrintPrec lvl p typ <+>
        pPrintPrec lvl p row

instance SubTreeConstraint Typ k Pretty => Pretty (Typ k) where
    pPrintPrec _ _ TInt = Pretty.text "Int"
    pPrintPrec lvl p (TFun x) = pPrintPrec lvl p x
    pPrintPrec lvl p (TRec x) = pPrintPrec lvl p x
    pPrintPrec _ _ (TVar s) = pPrint s

instance SubTreeConstraint Row k Pretty => Pretty (Row k) where
    pPrintPrec _ _ REmpty = Pretty.text "{}"
    pPrintPrec lvl p (RExtend (RowExtend k v r)) =
        pPrintPrec lvl 20 k <+>
        Pretty.text ":" <+>
        pPrintPrec lvl 2 v <+>
        Pretty.text ":*:" <+>
        pPrintPrec lvl 1 r
        & maybeParens (p > 1)
    pPrintPrec _ _ (RVar s) = pPrint s

instance HasChild Types Typ where getChild = tTyp
instance HasChild Types Row where getChild = tRow

instance PartialOrd RConstraints where
    RowConstraints f0 s0 `leq` RowConstraints f1 s1 = f0 `leq` f1 && s0 `leq` s1

instance JoinSemiLattice RConstraints where
    RowConstraints f0 s0 \/ RowConstraints f1 s1 = RowConstraints (f0 \/ f1) (s0 \/ s1)

instance RowConstraints RConstraints where
    type RowConstraintsKey RConstraints = Name
    forbidden = rForbiddenFields

instance HasTypeConstraints Typ where
    type TypeConstraintsOf Typ = ScopeLevel
    applyConstraints _ _ _ _ TInt = pure TInt
    applyConstraints _ _ _ _ (TVar v) = TVar v & pure
    applyConstraints _ c _ u (TFun f) = monoChildren (u c) f <&> TFun
    applyConstraints _ c _ u (TRec r) = u (RowConstraints mempty c) r <&> TRec

instance HasTypeConstraints Row where
    type TypeConstraintsOf Row = RConstraints
    applyConstraints _ _ _ _ REmpty = pure REmpty
    applyConstraints _ _ _ _ (RVar x) = RVar x & pure
    applyConstraints p c e u (RExtend x) =
        applyRowConstraints p c (^. rScope) (e . (`RowConstraints` mempty) . singleton) u x <&> RExtend

type PureInferState = (Tree Types PureBinding, Tree Types (Const Int))

emptyPureInferState :: PureInferState
emptyPureInferState =
    ( Types emptyPureBinding emptyPureBinding
    , Types (Const 0) (Const 0)
    )

type STInferState s = Tree Types (Const (STRef s Int))

type instance SchemeType (Tree Pure Typ) = Typ
instance Recursive (Unify m) Typ => Instantiate m (Tree Pure Typ)

instance HasQuantifiedVar Typ where
    type QVar Typ = Name
    quantifiedVar = _TVar

instance HasQuantifiedVar Row where
    type QVar Row = Name
    quantifiedVar = _RVar

instance HasFuncType Typ where
    funcType = _TFun

instance HasScopeTypes v Typ a => HasScopeTypes v Typ (a, x) where
    scopeTypes = Lens._1 . scopeTypes

instance HasScopeTypes v Typ a => HasScopeTypes v Typ (a, x, y) where
    scopeTypes = Lens._1 . scopeTypes

rStructureMismatch ::
    Recursive (Unify m) Row =>
    Tree (UTermBody (UVar m)) Row -> Tree (UTermBody (UVar m)) Row -> m ()
rStructureMismatch (UTermBody c0 (RExtend r0)) (UTermBody c1 (RExtend r1)) =
    rowStructureMismatch (newTerm . RExtend) (c0, r0) (c1, r1)
rStructureMismatch x y = unifyError (Mismatch (x ^. uBody) (y ^. uBody))
