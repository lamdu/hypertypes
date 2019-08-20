{-# LANGUAGE TemplateHaskell, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE RankNTypes, DerivingVia, UndecidableInstances #-}

module TypeLang where

import           AST
import           AST.Class.Has
import           AST.Class.Unify
import           AST.Infer
import           AST.Term.FuncType
import           AST.Term.NamelessScope
import           AST.Term.Nominal
import           AST.Term.Row
import           AST.Term.Scheme
import           AST.Unify
import           AST.Unify.Binding
import           AST.Unify.QuantifiedVar
import           AST.Unify.Term
import           Algebra.PartialOrd
import           Control.Applicative
import           Control.Lens (ALens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader (MonadReader)
import           Control.Monad.ST.Class (MonadST(..))
import           Data.STRef
import           Data.Set (Set, singleton)
import           Generic.Data
import           Generics.OneLiner (Constraints)
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude

newtype Name = Name String deriving stock (Eq, Ord, Show)

data Typ k
    = TInt
    | TFun (FuncType Typ k)
    | TRec (Node k Row)
    | TVar Name
    | TNom (NominalInst Name Types k)
    deriving Generic

data Row k
    = REmpty
    | RExtend (RowExtend Name Typ Row k)
    | RVar Name

data RConstraints = RowConstraints
    { _rForbiddenFields :: Set Name
    , _rScope :: ScopeLevel
    } deriving stock (Eq, Show, Generic)
    deriving (Semigroup, Monoid) via Generically RConstraints

data Types k = Types
    { _tTyp :: Node k Typ
    , _tRow :: Node k Row
    } deriving Generic

data TypeError k
    = TypError (UnifyError Typ k)
    | RowError (UnifyError Row k)
    | QVarNotInScope Name
    deriving Generic

Lens.makePrisms ''Typ
Lens.makePrisms ''Row
Lens.makePrisms ''TypeError
Lens.makeLenses ''RConstraints
Lens.makeLenses ''Types

instance KHas (ANode Typ) Types where
    hasK = MkANode . (^. tTyp)

instance KHas (Product (ANode Typ) (ANode Row)) Types where
    hasK (Types t0 r0) = Pair (MkANode t0) (MkANode r0)

instance KNodes Types where
    type NodeTypesOf Types = Types
    type NodesConstraint Types = ConcatConstraintFuncs '[On Typ, On Row]
instance KNodes Typ where
    type NodeTypesOf Typ = Types
instance KNodes Row where
    type NodeTypesOf Row = Types

makeZipMatch ''Typ
makeZipMatch ''Row
makeZipMatch ''Types
makeKTraversableAndBases ''Typ
makeKTraversableAndBases ''Row
makeKApplicativeBases ''Types
makeKTraversableAndFoldable ''Types

type instance NomVarTypes Typ = Types

instance HasNominalInst Name Typ where nominalInst = _TNom

instance Pretty Name where
    pPrint (Name x) = Pretty.text x

instance Pretty RConstraints where
    pPrintPrec _ p (RowConstraints f _) =
        Pretty.text "Forbidden fields:" <+> pPrint (f ^.. Lens.folded)
        & maybeParens (p > 10)

instance Constraints (Types k) Pretty => Pretty (Types k) where
    pPrintPrec lvl p (Types typ row) =
        pPrintPrec lvl p typ <+>
        pPrintPrec lvl p row

instance Constraints (TypeError k) Pretty => Pretty (TypeError k) where
    pPrintPrec lvl p (TypError x) = pPrintPrec lvl p x
    pPrintPrec lvl p (RowError x) = pPrintPrec lvl p x
    pPrintPrec _ _ (QVarNotInScope x) =
        Pretty.text "quantified type variable not in scope" <+> pPrint x

instance Constraints (Typ k) Pretty => Pretty (Typ k) where
    pPrintPrec _ _ TInt = Pretty.text "Int"
    pPrintPrec lvl p (TFun x) = pPrintPrec lvl p x
    pPrintPrec lvl p (TRec x) = pPrintPrec lvl p x
    pPrintPrec _ _ (TVar s) = pPrint s
    pPrintPrec _ _ (TNom n) = pPrint n

instance Constraints (Types k) Pretty => Pretty (Row k) where
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

instance TypeConstraints RConstraints where
    generalizeConstraints = rScope .~ mempty
    toScopeConstraints = rForbiddenFields .~ mempty

instance RowConstraints RConstraints where
    type RowConstraintsKey RConstraints = Name
    forbidden = rForbiddenFields

type instance TypeConstraintsOf Typ = ScopeLevel

instance HasTypeConstraints Typ where
    verifyConstraints _ _ _ TInt = pure TInt
    verifyConstraints _ _ _ (TVar v) = TVar v & pure
    verifyConstraints c _ u (TFun f) = traverseK1 (u c) f <&> TFun
    verifyConstraints c _ u (TRec r) = u (RowConstraints mempty c) r <&> TRec
    verifyConstraints c _ u (TNom (NominalInst n (Types t r))) =
        Types
        <$> (_QVarInstances . traverse) (u c) t
        <*> (_QVarInstances . traverse) (u (RowConstraints mempty c)) r
        <&> NominalInst n <&> TNom

type instance TypeConstraintsOf Row = RConstraints

instance HasTypeConstraints Row where
    verifyConstraints _ _ _ REmpty = pure REmpty
    verifyConstraints _ _ _ (RVar x) = RVar x & pure
    verifyConstraints c e u (RExtend x) =
        applyRowExtendConstraints c (^. rScope) (e . (`RowConstraints` mempty) . singleton) u x <&> RExtend

type PureInferState = (Tree Types Binding, Tree Types UVar)

emptyPureInferState :: PureInferState
emptyPureInferState =
    ( Types emptyBinding emptyBinding
    , Types (UVar 0) (UVar 0)
    )

type STNameGen s = Tree Types (Const (STRef s Int))

instance (c Typ, c Row) => Recursively c Typ
instance (c Typ, c Row) => Recursively c Row

instance RFoldable Typ
instance RFoldable Row
instance RFunctor Typ
instance RFunctor Row
instance RTraversable Typ
instance RTraversable Row

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

instance Inferrable Typ where type InferOf Typ = ANode Typ
instance Inferrable Row where type InferOf Row = ANode Row
instance HasInferredValue Typ where inferredValue = _ANode
instance HasInferredValue Row where inferredValue = _ANode

instance
    (Monad m, MonadInstantiate m Typ, MonadInstantiate m Row) =>
    Infer m Typ where

    inferBody = inferType

instance
    (Monad m, MonadInstantiate m Typ, MonadInstantiate m Row) =>
    Infer m Row where

    inferBody = inferType

rStructureMismatch ::
    (Unify m Typ, Unify m Row) =>
    (forall c. Unify m c => Tree (UVarOf m) c -> Tree (UVarOf m) c -> m (Tree (UVarOf m) c)) ->
    Tree (UTermBody (UVarOf m)) Row -> Tree (UTermBody (UVarOf m)) Row -> m ()
rStructureMismatch match (UTermBody c0 (RExtend r0)) (UTermBody c1 (RExtend r1)) =
    rowExtendStructureMismatch match _RExtend (c0, r0) (c1, r1)
rStructureMismatch _ x y = unifyError (Mismatch (x ^. uBody) (y ^. uBody))

readModifySTRef :: MonadST m => STRef (World m) a -> (a -> a) -> m a
readModifySTRef ref func =
    do
        old <- readSTRef ref
        old <$ (writeSTRef ref $! func old)
        & liftST

newStQuantified ::
    (MonadReader env m, MonadST m, Enum a) =>
    ALens' env (Const (STRef (World m) a) (ast :: Knot)) ->
    m a
newStQuantified l =
    Lens.view (Lens.cloneLens l . Lens._Wrapped)
    >>= (`readModifySTRef` succ)

deriving instance Constraints (Types k) Eq   => Eq   (Typ k)
deriving instance Constraints (Types k) Eq   => Eq   (Row k)
deriving instance Constraints (Types k) Eq   => Eq   (Types k)
deriving instance Constraints (Types k) Eq   => Eq   (TypeError k)
deriving instance Constraints (Types k) Show => Show (Typ k)
deriving instance Constraints (Types k) Show => Show (Row k)
deriving instance Constraints (Types k) Show => Show (Types k)
deriving instance Constraints (Types k) Show => Show (TypeError k)
