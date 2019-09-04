-- | Nominal (named) types declaration, instantiation, construction, and access.

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, TypeOperators, GADTs, EmptyCase #-}
{-# LANGUAGE RankNTypes #-}

module AST.Term.Nominal
    ( NominalDecl(..), nParams, nScheme, KWitness(..)
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
import           AST.TH.Internal.Instances (makeCommonInstances)
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
import           Generics.Constraints (Constraints)
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
--
-- Wrap content with a data constructor
-- (analogues to a data constructor of a Haskell `newtype`'s).
--
-- Introduces the nominal's foralled type variables into the value's scope.
data ToNom nomId term k = ToNom
    { _tnId :: nomId
    , _tnVal :: Node k term
    } deriving Generic

-- | Access the data in a nominally typed value.
--
-- Analogues to a getter of a Haskell `newtype`.
newtype FromNom nomId (term :: Knot -> *) (k :: Knot) = FromNom nomId
    deriving newtype (Eq, Ord, Binary, NFData)
    deriving stock (Show, Generic)

-- | A nominal declaration loaded into scope in an inference monad.
data LoadedNominalDecl typ v = LoadedNominalDecl
    { _lnParams :: Tree (NomVarTypes typ) (QVarInstances (RunKnot v))
    , _lnForalls :: Tree (NomVarTypes typ) (QVarInstances (RunKnot v))
    , _lnType :: Tree (GTerm (RunKnot v)) typ
    } deriving Generic

makeLenses ''NominalDecl
makeLenses ''NominalInst
makeLenses ''ToNom
makePrisms ''FromNom
makeCommonInstances [''NominalDecl, ''NominalInst, ''ToNom, ''LoadedNominalDecl]
makeKTraversableAndBases ''NominalDecl
makeKTraversableApplyAndBases ''ToNom
makeKTraversableApplyAndBases ''FromNom

instance KNodes v => KNodes (NominalInst n v) where
    type KNodesConstraint (NominalInst n v) c = KNodesConstraint v c
    data KWitness (NominalInst n v) c = KW_NominalInst (KWitness v c)
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (KW_NominalInst w) = kLiftConstraint w
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p =
        withDict (kCombineConstraints (p0 p)) Dict
        where
            p0 :: Proxy (And a b (NominalInst n v)) -> Proxy (And a b v)
            p0 _ = Proxy

instance KFunctor v => KFunctor (NominalInst n v) where
    {-# INLINE mapK #-}
    mapK f = nArgs %~ mapK (\w -> _QVarInstances . Lens.mapped %~ f (KW_NominalInst w))

instance KFoldable v => KFoldable (NominalInst n v) where
    {-# INLINE foldMapK #-}
    foldMapK f =
        foldMapK (\w -> foldMap (f (KW_NominalInst w)) . (^. _QVarInstances)) . (^. nArgs)

instance KTraversable v => KTraversable (NominalInst n v) where
    {-# INLINE sequenceK #-}
    sequenceK (NominalInst n v) =
        traverseK (const (_QVarInstances (traverse runContainedK))) v
        <&> NominalInst n

instance
    ( Eq nomId
    , ZipMatch varTypes
    , KTraversable varTypes
    , KNodesConstraint varTypes ZipMatch
    , KNodesConstraint varTypes OrdQVar
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
    , KNodesConstraint varTypes (PrettyConstraints k)
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

instance (RNodes typ, KNodes (NomVarTypes typ)) => KNodes (LoadedNominalDecl typ) where
    type KNodesConstraint (LoadedNominalDecl typ) c =
        ( KNodesConstraint (NomVarTypes typ) c
        , c typ
        , Recursive c
        )
    data KWitness (LoadedNominalDecl typ) n where
        KW_LoadedNominalDecl_E0 :: KRecWitness typ n -> KWitness (LoadedNominalDecl typ) n
        KW_LoadedNominalDecl_E1 :: KWitness (NomVarTypes typ) n -> KWitness (LoadedNominalDecl typ) n
    {-# INLINE kLiftConstraint #-}
    kLiftConstraint (KW_LoadedNominalDecl_E0 w) = kLiftConstraint (KW_Flip_GTerm w)
    kLiftConstraint (KW_LoadedNominalDecl_E1 w) = kLiftConstraint w
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints p =
        withDict (kCombineConstraints (p0 p)) Dict
        where
            p0 :: Proxy (c (LoadedNominalDecl typ)) -> Proxy (c (NomVarTypes typ))
            p0 _ = Proxy

instance
    (RFunctor typ, KFunctor (NomVarTypes typ)) =>
    KFunctor (LoadedNominalDecl typ) where
    {-# INLINE mapK #-}
    mapK f (LoadedNominalDecl mp mf t) =
        LoadedNominalDecl (onMap mp) (onMap mf)
        (t & Lens.from _Flip %~ mapK (\(KW_Flip_GTerm w) -> f (KW_LoadedNominalDecl_E0 w)))
        where
            onMap = mapK (\w -> _QVarInstances . Lens.mapped %~ f (KW_LoadedNominalDecl_E1 w))

instance
    (RFoldable typ, KFoldable (NomVarTypes typ)) =>
    KFoldable (LoadedNominalDecl typ) where
    {-# INLINE foldMapK #-}
    foldMapK f (LoadedNominalDecl mp mf t) =
        onMap mp <> onMap mf <>
        foldMapK (\(KW_Flip_GTerm w) -> f (KW_LoadedNominalDecl_E0 w)) (_Flip # t)
        where
            onMap = foldMapK (\w -> foldMap (f (KW_LoadedNominalDecl_E1 w)) . (^. _QVarInstances))

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
            onMap = traverseK (const ((_QVarInstances . traverse) runContainedK))

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
        case traverseK (const (^? _GMono)) x of
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
    , KNodesConstraint (NomVarTypes typ) (Unify m)
    , HasScheme (NomVarTypes typ) m typ
    ) =>
    Tree Pure (NominalDecl typ) ->
    m (Tree (LoadedNominalDecl typ) (UVarOf m))
loadNominalDecl (Pure (NominalDecl params (Scheme foralls typ))) =
    do
        paramsL <- traverseKWith (Proxy @(Unify m)) makeQVarInstances params
        forallsL <- traverseKWith (Proxy @(Unify m)) makeQVarInstances foralls
        wrapM (Proxy @(HasScheme (NomVarTypes typ) m))
            (loadBody paramsL forallsL) typ
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
    , KNodesConstraint varTypes (Unify m)
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

type instance InferOf (ToNom n e) = NominalInst n (NomVarTypes (TypeOf e))

instance
    ( MonadScopeLevel m
    , MonadNominals nomId (TypeOf expr) m
    , KTraversable (NomVarTypes (TypeOf expr))
    , KNodesConstraint (NomVarTypes (TypeOf expr)) (Unify m)
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
            (ToNom nomId valI, NominalInst nomId paramsT)
                <$ unify typ (valR ^# inferredType (Proxy @expr))

type instance InferOf (FromNom n e) = FuncType (TypeOf e)

instance
    ( Infer m expr
    , HasNominalInst nomId (TypeOf expr)
    , MonadNominals nomId (TypeOf expr) m
    , KTraversable (NomVarTypes (TypeOf expr))
    , KNodesConstraint (NomVarTypes (TypeOf expr)) (Unify m)
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
        <&> (FromNom nomId, )
