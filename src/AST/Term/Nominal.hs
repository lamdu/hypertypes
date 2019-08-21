{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, TypeOperators #-}

module AST.Term.Nominal
    ( NominalDecl(..), nParams, nScheme
    , NominalInst(..), nId, nArgs
    , ToNom(..), tnId, tnVal
    , FromNom(..), _FromNom

    , HasNominalInst(..)
    , NomVarTypes
    , MonadNominals(..)
    , LoadedNominalDecl, loadNominalDecl
    ) where

import           AST
import           AST.Class.Has (HasChild(..))
import           AST.Class.Foldable (foldMapKWith, traverseKWith_)
import           AST.Class.Recursive
import           AST.Class.Traversable (ContainedK(..))
import           AST.Class.ZipMatch (ZipMatch(..))
import           AST.Combinator.Flip (_Flip)
import           AST.Infer
import           AST.Term.FuncType (FuncType(..))
import           AST.Term.Map (TermMap(..), _TermMap)
import           AST.Term.Scheme
import           AST.Unify
import           AST.Unify.Generalize (GTerm(..), _GMono, instantiateWith, instantiateForAll)
import           AST.Unify.New (newTerm)
import           AST.Unify.QuantifiedVar (HasQuantifiedVar(..), OrdQVar)
import           AST.Unify.Term (UTerm(..))
import           Control.Applicative (Alternative(..))
import           Control.DeepSeq (NFData)
import           Control.Lens (Prism', makeLenses, makePrisms)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Writer (execWriterT)
import           Data.Binary (Binary)
import           Data.Constraint (Dict(..), withDict)
import           Data.Foldable (traverse_)
import           Data.Kind (Type)
import           Data.Proxy (Proxy(..))
import qualified Data.Map as Map
import           Generics.OneLiner (Constraints)
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

type family NomVarTypes (t :: Knot -> Type) :: Knot -> Type

-- | A declaration of a nominal type.
data NominalDecl typ k = NominalDecl
    { _nParams :: Tree (NomVarTypes typ) QVars
    , _nScheme :: Scheme (NomVarTypes typ) typ k
    } deriving Generic

-- | An instantiation of a nominal type
data NominalInst nomId varTypes k = NominalInst
    { _nId :: nomId
    , _nArgs :: Tree varTypes (QVarInstances (RunKnot k))
    } deriving Generic

-- | Nominal data constructor.
-- Wraps the content of a nominal with its data constructor.
-- Introduces the nominal's forall type variables into the value's scope.
data ToNom nomId term k = ToNom
    { _tnId :: nomId
    , _tnVal :: Node k term
    } deriving Generic

newtype FromNom nomId (term :: Knot -> *) (k :: Knot) = FromNom nomId
    deriving newtype (Eq, Ord, Binary, NFData)
    deriving stock (Show, Generic)

instance KNodes v => KNodes (NominalInst n v) where
    type NodesConstraint (NominalInst n v) c = NodesConstraint v c
    {-# INLINE kNoConstraints #-}
    kNoConstraints _ = withDict (kNoConstraints (Proxy @v)) Dict
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p =
        withDict (kCombineConstraints (p0 p)) Dict
        where
            p0 :: Proxy (And a b (NominalInst n v)) -> Proxy (And a b v)
            p0 _ = Proxy

makeLenses ''NominalDecl
makeLenses ''NominalInst
makeLenses ''ToNom
makePrisms ''FromNom
makeKTraversableAndBases ''NominalDecl
makeKTraversableApplyAndBases ''ToNom
makeKTraversableApplyAndBases ''FromNom

instance KFunctor v => KFunctor (NominalInst n v) where
    {-# INLINE mapKWith #-}
    mapKWith p f (NominalInst n v) =
        mapKWith p (_QVarInstances . Lens.mapped %~ f) v & NominalInst n

instance KFoldable v => KFoldable (NominalInst n v) where
    {-# INLINE foldMapKWith #-}
    foldMapKWith p f = foldMapKWith p (foldMap f . (^. _QVarInstances)) . (^. nArgs)

instance KTraversable v => KTraversable (NominalInst n v) where
    {-# INLINE sequenceK #-}
    sequenceK (NominalInst n v) =
        traverseK (_QVarInstances (traverse runContainedK)) v
        <&> NominalInst n

instance
    ( Eq nomId
    , ZipMatch varTypes
    , KTraversable varTypes
    , NodesConstraint varTypes ZipMatch
    , NodesConstraint varTypes OrdQVar
    ) =>
    ZipMatch (NominalInst nomId varTypes) where

    {-# INLINE zipMatch #-}
    zipMatch (NominalInst xId x) (NominalInst yId y)
        | xId /= yId = Nothing
        | otherwise =
            withDict (kCombineConstraints (Proxy @(And ZipMatch OrdQVar varTypes))) $
            zipMatch x y
            >>= traverseKWith (Proxy @(ZipMatch `And` OrdQVar))
                (\(Pair (QVarInstances c0) (QVarInstances c1)) ->
                    zipMatch (TermMap c0) (TermMap c1)
                    <&> (^. _TermMap)
                    <&> QVarInstances
                )
            <&> NominalInst xId

instance Constraints (ToNom nomId term k) Pretty => Pretty (ToNom nomId term k) where
    pPrintPrec lvl p (ToNom nomId term) =
        (pPrint nomId <> Pretty.text "#") <+> pPrintPrec lvl 11 term
        & maybeParens (p > 10)

class    (Pretty (QVar k), Pretty (Node outer k)) => PrettyConstraints outer k
instance (Pretty (QVar k), Pretty (Node outer k)) => PrettyConstraints outer k

instance
    ( Pretty nomId
    , KApply varTypes, KFoldable varTypes
    , NodesConstraint varTypes (PrettyConstraints k)
    ) =>
    Pretty (NominalInst nomId varTypes k) where

    pPrint (NominalInst n vars) =
        pPrint n <>
        joinArgs
        (foldMapKWith (Proxy @(PrettyConstraints k)) mkArgs vars)
        where
            joinArgs [] = mempty
            joinArgs xs =
                Pretty.text "[" <>
                Pretty.sep (Pretty.punctuate (Pretty.text ",") xs)
                <> Pretty.text "]"
            mkArgs (QVarInstances m) =
                Map.toList m <&>
                \(k, v) ->
                (pPrint k <> Pretty.text ":") <+> pPrint v

data LoadedNominalDecl typ v = LoadedNominalDecl
    { _lnParams :: Tree (NomVarTypes typ) (QVarInstances (RunKnot v))
    , _lnForalls :: Tree (NomVarTypes typ) (QVarInstances (RunKnot v))
    , _lnType :: Tree (GTerm (RunKnot v)) typ
    } deriving Generic

instance KNodes (NomVarTypes typ) => KNodes (LoadedNominalDecl typ) where
    type NodesConstraint (LoadedNominalDecl typ) c =
        ( NodesConstraint (NomVarTypes typ) c
        , c typ
        , Recursive c
        )
    {-# INLINE kNoConstraints #-}
    kNoConstraints _ =
        withDict (kNoConstraints (Proxy @(NomVarTypes typ))) Dict
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p =
        withDict (kCombineConstraints (p0 p)) Dict
        where
            p0 :: Proxy (c (LoadedNominalDecl typ)) -> Proxy (c (NomVarTypes typ))
            p0 _ = Proxy

instance
    (RFunctor typ, KFunctor (NomVarTypes typ)) =>
    KFunctor (LoadedNominalDecl typ) where
    {-# INLINE mapKWith #-}
    mapKWith c f (LoadedNominalDecl mp mf t) =
        LoadedNominalDecl (onMap mp) (onMap mf)
        (t & Lens.from _Flip %~ mapKWith c f)
        where
            onMap = mapKWith c (_QVarInstances . Lens.mapped %~ f)

instance
    (RFoldable typ, KFoldable (NomVarTypes typ)) =>
    KFoldable (LoadedNominalDecl typ) where
    {-# INLINE foldMapKWith #-}
    foldMapKWith c f (LoadedNominalDecl mp mf t) =
        onMap mp <> onMap mf <> foldMapKWith c f (_Flip # t)
        where
            onMap = foldMapKWith c (^. _QVarInstances . Lens.folded . Lens.to f)

instance
    (RTraversable typ, KTraversable (NomVarTypes typ)) =>
    KTraversable (LoadedNominalDecl typ) where
    {-# INLINE sequenceK #-}
    sequenceK (LoadedNominalDecl p f t) =
        LoadedNominalDecl
        <$> onMap p
        <*> onMap f
        <*> Lens.from _Flip sequenceK t
        where
            onMap = traverseK ((_QVarInstances . traverse) runContainedK)

{-# INLINE loadBody #-}
loadBody ::
    ( Unify m typ
    , HasChild varTypes typ
    , Ord (QVar typ)
    ) =>
    Tree varTypes (QVarInstances (UVarOf m)) ->
    Tree varTypes (QVarInstances (UVarOf m)) ->
    Tree typ (GTerm (UVarOf m)) ->
    m (Tree (GTerm (UVarOf m)) typ)
loadBody params foralls x =
    case x ^? quantifiedVar >>= get of
    Just r -> GPoly r & pure
    Nothing ->
        case traverseK (^? _GMono) x of
        Just xm -> newTerm xm <&> GMono
        Nothing -> GBody x & pure
    where
        get v =
            params ^? getChild . _QVarInstances . Lens.ix v <|>
            foralls ^? getChild . _QVarInstances . Lens.ix v

{-# INLINE loadNominalDecl #-}
loadNominalDecl ::
    forall m typ.
    ( Monad m
    , KTraversable (NomVarTypes typ)
    , NodesConstraint (NomVarTypes typ) (Unify m)
    , HasScheme (NomVarTypes typ) m typ
    ) =>
    Tree Pure (NominalDecl typ) ->
    m (Tree (LoadedNominalDecl typ) (UVarOf m))
loadNominalDecl (MkPure (NominalDecl params (Scheme foralls typ))) =
    do
        paramsL <- traverseKWith (Proxy @(Unify m)) makeQVarInstances params
        forallsL <- traverseKWith (Proxy @(Unify m)) makeQVarInstances foralls
        wrapM (Proxy @(HasScheme (NomVarTypes typ) m))
            Dict (loadBody paramsL forallsL) typ
            <&> LoadedNominalDecl paramsL forallsL

class MonadNominals nomId typ m where
    getNominalDecl :: nomId -> m (Tree (LoadedNominalDecl typ) (UVarOf m))

class HasNominalInst nomId typ where
    nominalInst :: Prism' (Tree typ k) (Tree (NominalInst nomId (NomVarTypes typ)) k)

{-# INLINE lookupParams #-}
lookupParams ::
    forall m varTypes.
    ( Applicative m
    , KTraversable varTypes
    , NodesConstraint varTypes (Unify m)
    ) =>
    Tree varTypes (QVarInstances (UVarOf m)) ->
    m (Tree varTypes (QVarInstances (UVarOf m)))
lookupParams =
    traverseKWith (Proxy @(Unify m)) ((_QVarInstances . traverse) lookupParam)
    where
        lookupParam v =
            lookupVar binding v
            >>=
            \case
            UInstantiated r -> pure r
            USkolem l ->
                -- This is a phantom-type, wasn't instantiated by `instantiate`.
                scopeConstraints <&> (<> l) >>= newVar binding . UUnbound
            _ -> error "unexpected state at nominal's parameter"

instance
    (Inferrable e, KTraversable (NomVarTypes (TypeOf e))) =>
    Inferrable (ToNom n e) where
    type InferOf (ToNom n e) = NominalInst n (NomVarTypes (TypeOf e))

instance
    ( MonadScopeLevel m
    , MonadNominals nomId (TypeOf expr) m
    , KTraversable (NomVarTypes (TypeOf expr))
    , NodesConstraint (NomVarTypes (TypeOf expr)) (Unify m)
    , Unify m (TypeOf expr)
    , HasInferredType expr
    , Infer m expr
    ) =>
    Infer m (ToNom nomId expr) where

    {-# INLINE inferBody #-}
    inferBody (ToNom nomId val) =
        do
            (InferredChild valI valR, typ, paramsT) <-
                do
                    v <- inferChild val
                    LoadedNominalDecl params foralls gen <- getNominalDecl nomId
                    recover <-
                        traverseKWith_ (Proxy @(Unify m))
                        (traverse_ (instantiateForAll USkolem) . (^. _QVarInstances))
                        foralls
                        & execWriterT
                    (typ, paramsT) <- instantiateWith (lookupParams params) UUnbound gen
                    (v, typ, paramsT) <$ sequence_ recover
                & localLevel
            _ <- unify typ (valR ^# inferredType (Proxy @expr))
            InferRes (ToNom nomId valI) (NominalInst nomId paramsT) & pure

instance Inferrable (FromNom n e) where type InferOf (FromNom n e) = FuncType (TypeOf e)

instance
    ( Infer m expr
    , HasNominalInst nomId (TypeOf expr)
    , MonadNominals nomId (TypeOf expr) m
    , KTraversable (NomVarTypes (TypeOf expr))
    , NodesConstraint (NomVarTypes (TypeOf expr)) (Unify m)
    , Unify m (TypeOf expr)
    ) =>
    Infer m (FromNom nomId expr) where

    {-# INLINE inferBody #-}
    inferBody (FromNom nomId) =
        do
            LoadedNominalDecl params _ gen <- getNominalDecl nomId
            (typ, paramsT) <- instantiateWith (lookupParams params) UUnbound gen
            nominalInst # NominalInst nomId paramsT & newTerm
                <&> (`FuncType` typ)
        <&> InferRes (FromNom nomId)

deriving instance Constraints (NominalDecl t k) Eq   => Eq   (NominalDecl t k)
deriving instance Constraints (NominalDecl t k) Ord  => Ord  (NominalDecl t k)
deriving instance Constraints (NominalDecl t k) Show => Show (NominalDecl t k)
instance Constraints (NominalDecl t k) Binary => Binary (NominalDecl t k)
instance Constraints (NominalDecl t k) NFData => NFData (NominalDecl t k)

deriving instance Constraints (NominalInst n v k) Eq   => Eq   (NominalInst n v k)
deriving instance Constraints (NominalInst n v k) Ord  => Ord  (NominalInst n v k)
deriving instance Constraints (NominalInst n v k) Show => Show (NominalInst n v k)
instance Constraints (NominalInst n v k) Binary => Binary (NominalInst n v k)
instance Constraints (NominalInst n v k) NFData => NFData (NominalInst n v k)

deriving instance Constraints (ToNom n t k) Eq   => Eq   (ToNom n t k)
deriving instance Constraints (ToNom n t k) Ord  => Ord  (ToNom n t k)
deriving instance Constraints (ToNom n t k) Show => Show (ToNom n t k)
instance Constraints (ToNom n t k) Binary => Binary (ToNom n t k)
instance Constraints (ToNom n t k) NFData => NFData (ToNom n t k)

deriving instance Constraints (LoadedNominalDecl t k) Eq   => Eq   (LoadedNominalDecl t k)
deriving instance Constraints (LoadedNominalDecl t k) Ord  => Ord  (LoadedNominalDecl t k)
deriving instance Constraints (LoadedNominalDecl t k) Show => Show (LoadedNominalDecl t k)
instance Constraints (LoadedNominalDecl t k) Binary => Binary (LoadedNominalDecl t k)
instance Constraints (LoadedNominalDecl t k) NFData => NFData (LoadedNominalDecl t k)
