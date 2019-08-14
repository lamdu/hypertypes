{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TemplateHaskell #-}
{-# LANGUAGE RankNTypes, UndecidableSuperClasses #-}

module AST.Term.Nominal
    ( NominalDecl(..), nParams, nScheme
    , NominalInst(..), nId, nArgs
    , ToNom(..), tnId, tnVal
    , FromNom(..), _FromNom

    , HasNominalInst(..)
    , NomVarTypes
    , MonadNominals(..)
    , LoadedNominalDecl, loadNominalDecl
    , applyNominal
    ) where

import           AST
import           AST.Class (_MapK)
import           AST.Class.Has (HasChild(..))
import           AST.Class.Foldable (_ConvertK, foldMapKWith, traverseKWith_)
import           AST.Class.Recursive
import           AST.Class.Traversable (ContainedK(..))
import           AST.Class.ZipMatch (ZipMatch(..))
import           AST.Combinator.ANode (ANode)
import           AST.Infer
import           AST.Term.FuncType (FuncType(..))
import           AST.Term.Map (TermMap(..), _TermMap)
import           AST.Term.Scheme
import           AST.Unify
import           AST.Unify.Generalize (GTerm(..), _GMono, instantiateWith, instantiateForAll)
import           AST.Unify.New (newTerm)
import           AST.Unify.QuantifiedVar (HasQuantifiedVar(..), QVarHasInstance)
import           AST.Unify.Term (UTerm(..))
import           Control.Applicative (Alternative(..))
import           Control.DeepSeq (NFData)
import           Control.Lens (Prism', makeLenses, makePrisms)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Writer (execWriterT)
import           Data.Binary (Binary)
import           Data.Constraint (Constraint, Dict(..), withDict)
import           Data.Foldable (traverse_)
import           Data.Functor.Const (Const)
import           Data.Proxy (Proxy(..))
import qualified Data.Map as Map
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

type family NomVarTypes (typ :: Knot -> *) :: Knot -> *

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

instance KNodes (NominalDecl t) where
    type NodeTypesOf (NominalDecl t) = ANode t
    {-# INLINE combineConstraints #-}
    combineConstraints _ _ _ = Dict

instance KNodes (ToNom n t) where
    type NodeTypesOf (ToNom n t) = ANode t
    {-# INLINE combineConstraints #-}
    combineConstraints _ _ _ = Dict

instance KNodes (FromNom n t) where
    type NodeTypesOf (FromNom n t) = Const ()
    {-# INLINE combineConstraints #-}
    combineConstraints _ _ _ = Dict

instance KNodes v => KNodes (NominalInst n v) where
    type NodeTypesOf (NominalInst n v) = NodeTypesOf v
    {-# INLINE kNodes #-}
    kNodes _ = withDict (kNodes (Proxy @v)) Dict
    {-# INLINE combineConstraints #-}
    combineConstraints _ c0 c1 =
        withDict (kNodes (Proxy @v)) $
        withDict (combineConstraints (Proxy @(NodeTypesOf v)) c0 c1) Dict

makeLenses ''NominalDecl
makeLenses ''NominalInst
makeLenses ''ToNom
makePrisms ''FromNom
makeKTraversableAndBases ''NominalDecl
makeKTraversableAndBases ''ToNom
makeKTraversableAndBases ''FromNom

instance (KFunctor v, KNodes v) => KFunctor (NominalInst n v) where
    mapC f (NominalInst n v) =
        withDict (kNodes (Proxy @v)) $
        mapC (mapK (_MapK %~ (_QVarInstances . Lens.mapped %~)) f) v & NominalInst n

instance (KFoldable v, KNodes v) => KFoldable (NominalInst n v) where
    foldMapC f (NominalInst _ v) =
        withDict (kNodes (Proxy @v)) $
        foldMapC (mapK (_ConvertK %~ \fq -> foldMap fq . (^. _QVarInstances)) f) v

instance (KTraversable v, KNodes v) => KTraversable (NominalInst n v) where
    sequenceC (NominalInst n v) =
        traverseK (_QVarInstances (traverse runContainedK)) v
        <&> NominalInst n

instance
    ( Eq nomId
    , ZipMatch varTypes
    , KTraversable varTypes
    , NodesConstraint varTypes $ ZipMatch
    , NodesConstraint varTypes $ QVarHasInstance Ord
    ) =>
    ZipMatch (NominalInst nomId varTypes) where

    {-# INLINE zipMatch #-}
    zipMatch (NominalInst xId x) (NominalInst yId y)
        | xId /= yId = Nothing
        | otherwise =
            zipMatch x y
            >>= traverseKWith (Proxy @'[ZipMatch, QVarHasInstance Ord])
                (\(Pair (QVarInstances c0) (QVarInstances c1)) ->
                    zipMatch (TermMap c0) (TermMap c1)
                    <&> (^. _TermMap)
                    <&> QVarInstances
                )
            <&> NominalInst xId

instance DepsT Pretty nomId term k => Pretty (ToNom nomId term k) where
    pPrintPrec lvl p (ToNom nomId term) =
        (pPrint nomId <> Pretty.text "#") <+> pPrintPrec lvl 11 term
        & maybeParens (p > 10)

class    constraint (Node outer k) => NodeHasConstraint constraint outer k
instance constraint (Node outer k) => NodeHasConstraint constraint outer k

instance
    ( Pretty nomId
    , KApply varTypes, KFoldable varTypes
    , NodesConstraint varTypes $ QVarHasInstance Pretty
    , NodesConstraint varTypes $ NodeHasConstraint Pretty k
    ) =>
    Pretty (NominalInst nomId varTypes k) where

    pPrint (NominalInst n vars) =
        pPrint n <>
        joinArgs
        (foldMapKWith (Proxy @[QVarHasInstance Pretty, NodeHasConstraint Pretty k]) mkArgs vars)
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
    , NodesConstraint (NomVarTypes typ) $ Unify m
    , RLiftConstraints typ '[Unify m, HasChild (NomVarTypes typ), QVarHasInstance Ord]
    ) =>
    Tree Pure (NominalDecl typ) ->
    m (Tree (LoadedNominalDecl typ) (UVarOf m))
loadNominalDecl (MkPure (NominalDecl params (Scheme foralls typ))) =
    do
        paramsL <- traverseKWith (Proxy @'[Unify m]) makeQVarInstances params
        forallsL <- traverseKWith (Proxy @'[Unify m]) makeQVarInstances foralls
        wrapM (Proxy @'[Unify m, HasChild (NomVarTypes typ), QVarHasInstance Ord])
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
    , NodesConstraint varTypes $ Unify m
    ) =>
    Tree varTypes (QVarInstances (UVarOf m)) ->
    m (Tree varTypes (QVarInstances (UVarOf m)))
lookupParams =
    traverseKWith (Proxy @'[Unify m]) ((_QVarInstances . traverse) lookupParam)
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

type instance InferOf (ToNom nomId expr) = NominalInst nomId (NomVarTypes (TypeOf expr))

instance
    ( MonadScopeLevel m
    , MonadNominals nomId (TypeOf expr) m
    , KTraversable (NomVarTypes (TypeOf expr))
    , NodesConstraint (NomVarTypes (TypeOf expr)) $ Unify m
    , Recursively KNodes (TypeOf expr)
    , Recursively (Unify m) (TypeOf expr)
    , HasInferredType expr
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
                        traverseKWith_ (Proxy @'[Unify m])
                        (traverse_ (instantiateForAll USkolem) . (^. _QVarInstances))
                        foralls
                        & execWriterT
                    (typ, paramsT) <- instantiateWith (lookupParams params) UUnbound gen
                    (v, typ, paramsT) <$ sequence_ recover
                & localLevel
            _ <- unify typ (valR ^# inferredType (Proxy @expr))
            InferRes (ToNom nomId valI) (NominalInst nomId paramsT) & pure

type instance InferOf (FromNom nomId expr) = FuncType (TypeOf expr)

instance
    ( Infer m expr
    , HasNominalInst nomId (TypeOf expr)
    , MonadNominals nomId (TypeOf expr) m
    , KTraversable (NomVarTypes (TypeOf expr))
    , NodesConstraint (NomVarTypes (TypeOf expr)) $ Unify m
    , Recursively KNodes (TypeOf expr)
    , Recursively (Unify m) (TypeOf expr)
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

-- | Get the scheme in a nominal given the parameters of a specific nominal instance.
applyNominal ::
    forall m k cs typ.
    (Monad m, RLiftConstraints typ cs) =>
    Proxy cs ->
    (forall n. ApplyConstraints cs n =>
        Dict (HasQuantifiedVar n, HasChild (NomVarTypes typ) n, QVarHasInstance Ord n, KTraversable n)
    ) ->
    (forall n. ApplyConstraints cs n => Tree n k -> m (Tree k n)) ->
    Tree Pure (NominalDecl typ) ->
    Tree (NomVarTypes typ) (QVarInstances k) ->
    m (Tree (Scheme (NomVarTypes typ) typ) k)
applyNominal _ getDeps mkType (MkPure (NominalDecl _paramsDecl scheme)) params =
    sTyp
    (subst (rLiftConstraints @typ @cs) getDeps mkType params)
    scheme

subst ::
    forall m typ cs varTypes k.
    Monad m =>
    Tree (RecursiveNodes typ) (KDict cs) ->
    (forall n. ApplyConstraints cs n =>
        Dict (HasQuantifiedVar n, HasChild varTypes n, QVarHasInstance Ord n, KTraversable n)
    ) ->
    (forall n. ApplyConstraints cs n => Tree n k -> m (Tree k n)) ->
    Tree varTypes (QVarInstances k) ->
    Tree Pure typ ->
    m (Tree k typ)
subst c getDeps mkType params (MkPure x) =
    withDict (c ^. recSelf . _KDict) $
    withDict
        (getDeps ::
            Dict (HasQuantifiedVar typ, HasChild varTypes typ, QVarHasInstance Ord typ, KTraversable typ)
        ) $
    case x ^? quantifiedVar of
    Just q ->
        params ^?
        getChild . _QVarInstances . Lens.ix q
        & maybe (mkType (quantifiedVar # q)) pure
    Nothing ->
        traverseKRec c (\d -> subst d getDeps mkType params) x
        >>= mkType

type DepsD c t k = ((c (Tree (NomVarTypes t) QVars), c (Node k t)) :: Constraint)
deriving instance DepsD Eq   t k => Eq   (NominalDecl t k)
deriving instance DepsD Ord  t k => Ord  (NominalDecl t k)
deriving instance DepsD Show t k => Show (NominalDecl t k)
instance DepsD Binary t k => Binary (NominalDecl t k)
instance DepsD NFData t k => NFData (NominalDecl t k)

type DepsI c n v k = ((c n, c (Tree v (QVarInstances (RunKnot k)))) :: Constraint)
deriving instance DepsI Eq   n v k => Eq   (NominalInst n v k)
deriving instance DepsI Ord  n v k => Ord  (NominalInst n v k)
deriving instance DepsI Show n v k => Show (NominalInst n v k)
instance DepsI Binary n v k => Binary (NominalInst n v k)
instance DepsI NFData n v k => NFData (NominalInst n v k)

type DepsT c n t k = ((c n, c (Node k t)) :: Constraint)
deriving instance DepsT Eq   n t k => Eq   (ToNom n t k)
deriving instance DepsT Ord  n t k => Ord  (ToNom n t k)
deriving instance DepsT Show n t k => Show (ToNom n t k)
instance DepsT Binary n t k => Binary (ToNom n t k)
instance DepsT NFData n t k => NFData (ToNom n t k)

type DepsL c t k =
    ( ( c (Tree (NomVarTypes t) (QVarInstances (RunKnot k)))
      , c (Tree (GTerm (RunKnot k)) t)
      ) :: Constraint
    )
deriving instance DepsL Eq   t k => Eq   (LoadedNominalDecl t k)
deriving instance DepsL Ord  t k => Ord  (LoadedNominalDecl t k)
deriving instance DepsL Show t k => Show (LoadedNominalDecl t k)
instance DepsL Binary t k => Binary (LoadedNominalDecl t k)
instance DepsL NFData t k => NFData (LoadedNominalDecl t k)
