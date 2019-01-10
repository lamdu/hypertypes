{-# LANGUAGE MultiParamTypeClasses, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, TypeOperators #-}

module TypeLang where

import           AST
import           AST.Class.HasChild
import           AST.Class.Infer.ScopeLevel
import           AST.Term.FuncType
import           AST.Term.Row
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
import           Data.Constraint (Constraint)
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

data TypeError k = TypError (UnifyError Typ k) | RowError (UnifyError Row k)

Lens.makePrisms ''Typ
Lens.makePrisms ''Row
Lens.makePrisms ''TypeError
Lens.makeLenses ''RConstraints
Lens.makeLenses ''Types
makeChildrenAndZipMatch ''Typ
makeChildrenAndZipMatch ''Row
makeChildren ''Types
makeChildren ''TypeError

type TypDeps cls k = ((cls (Tie k Typ), cls (Tie k Row)) :: Constraint)

deriving instance TypDeps Eq   k => Eq   (Typ k)
deriving instance TypDeps Eq   k => Eq   (Row k)
deriving instance TypDeps Eq   k => Eq   (TypeError k)
deriving instance TypDeps Show k => Show (Typ k)
deriving instance TypDeps Show k => Show (Row k)

instance Pretty Name where
    pPrint (Name x) = Pretty.text x

instance Pretty RConstraints where
    pPrint (RowConstraints f _) = Pretty.text "Forbidden fields:" <+> pPrint (f ^.. Lens.folded)

instance TypDeps Pretty k => Pretty (Types k) where
    pPrintPrec lvl p (Types typ row) =
        pPrintPrec lvl p typ <+>
        pPrintPrec lvl p row

instance TypDeps Pretty k => Pretty (TypeError k) where
    pPrint (TypError x) = pPrint x
    pPrint (RowError x) = pPrint x

instance TypDeps Pretty k => Pretty (Typ k) where
    pPrintPrec _ _ TInt = Pretty.text "Int"
    pPrintPrec lvl p (TFun x) = pPrintPrec lvl p x
    pPrintPrec lvl p (TRec x) = pPrintPrec lvl p x
    pPrintPrec _ _ (TVar s) = pPrint s

instance TypDeps Pretty k => Pretty (Row k) where
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

instance BoundedJoinSemiLattice RConstraints where
    bottom = RowConstraints bottom bottom

instance TypeConstraints RConstraints where
    generalizeConstraints = rScope .~ bottom

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
        applyRowExtendConstraints p c (^. rScope) (e . (`RowConstraints` bottom) . singleton) u x <&> RExtend

type PureInferState = (Tree Types PureBinding, Tree Types (Const Int))

emptyPureInferState :: PureInferState
emptyPureInferState =
    ( Types emptyPureBinding emptyPureBinding
    , Types (Const 0) (Const 0)
    )

type STInferState s = Tree Types (Const (STRef s Int))

instance (c Typ, c Row) => Recursive c Typ
instance (c Typ, c Row) => Recursive c Row

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
    (Unify m Typ, Unify m Row) =>
    Tree (UTermBody (UVar m)) Row -> Tree (UTermBody (UVar m)) Row -> m ()
rStructureMismatch (UTermBody c0 (RExtend r0)) (UTermBody c1 (RExtend r1)) =
    rowExtendStructureMismatch (newTerm . RExtend) (c0, r0) (c1, r1)
rStructureMismatch x y = unifyError (Mismatch (x ^. uBody) (y ^. uBody))
