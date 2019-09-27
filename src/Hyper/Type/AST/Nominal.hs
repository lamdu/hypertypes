-- | Nominal (named) types declaration, instantiation, construction, and access.

{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, EmptyCase #-}

module Hyper.Type.AST.Nominal
    ( NominalDecl(..), nParams, nScheme, HWitness(..)
    , NominalInst(..), nId, nArgs
    , ToNom(..), tnId, tnVal
    , FromNom(..), _FromNom

    , HasNominalInst(..)
    , NomVarTypes
    , MonadNominals(..)
    , LoadedNominalDecl, loadNominalDecl
    ) where

import           Control.Applicative (Alternative(..))
import           Control.DeepSeq (NFData)
import           Control.Lens (Prism', makeLenses, makePrisms)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Writer (execWriterT)
import           Data.Binary (Binary)
import           Data.Foldable (traverse_)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Generics.Constraints (Constraints)
import           Hyper
import           Hyper.Class.Has (HasChild(..))
import           Hyper.Class.Traversable (ContainedH(..))
import           Hyper.Class.ZipMatch (ZipMatch(..))
import           Hyper.Infer
import           Hyper.Recurse
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Type.AST.FuncType (FuncType(..))
import           Hyper.Type.AST.Map (TermMap(..), _TermMap)
import           Hyper.Type.AST.Scheme
import           Hyper.Type.Combinator.Flip (_Flip)
import           Hyper.Unify
import           Hyper.Unify.Generalize (GTerm(..), _GMono, instantiateWith, instantiateForAll)
import           Hyper.Unify.New (newTerm)
import           Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..), OrdQVar)
import           Hyper.Unify.Term (UTerm(..))
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

type family NomVarTypes (t :: HyperType) :: HyperType

-- | A declaration of a nominal type.
data NominalDecl typ h = NominalDecl
    { _nParams :: Tree (NomVarTypes typ) QVars
    , _nScheme :: Scheme (NomVarTypes typ) typ h
    } deriving Generic

-- | An instantiation of a nominal type
data NominalInst nomId varTypes h = NominalInst
    { _nId :: nomId
    , _nArgs :: Tree varTypes (QVarInstances (GetHyperType h))
    } deriving Generic

-- | Nominal data constructor.
--
-- Wrap content with a data constructor
-- (analogues to a data constructor of a Haskell `newtype`'s).
--
-- Introduces the nominal's foralled type variables into the value's scope.
data ToNom nomId term h = ToNom
    { _tnId :: nomId
    , _tnVal :: h # term
    } deriving Generic

-- | Access the data in a nominally typed value.
--
-- Analogues to a getter of a Haskell `newtype`.
newtype FromNom nomId (term :: HyperType) (h :: AHyperType) = FromNom nomId
    deriving newtype (Eq, Ord, Binary, NFData)
    deriving stock (Show, Generic)

-- | A nominal declaration loaded into scope in an inference monad.
data LoadedNominalDecl typ v = LoadedNominalDecl
    { _lnParams :: Tree (NomVarTypes typ) (QVarInstances (GetHyperType v))
    , _lnForalls :: Tree (NomVarTypes typ) (QVarInstances (GetHyperType v))
    , _lnType :: Tree (GTerm (GetHyperType v)) typ
    } deriving Generic

makeLenses ''NominalDecl
makeLenses ''NominalInst
makeLenses ''ToNom
makePrisms ''FromNom
makeCommonInstances [''NominalDecl, ''NominalInst, ''ToNom, ''LoadedNominalDecl]
makeHTraversableAndBases ''NominalDecl
makeHTraversableApplyAndBases ''ToNom
makeHTraversableApplyAndBases ''FromNom
makeZipMatch ''ToNom
makeZipMatch ''FromNom

instance HNodes v => HNodes (NominalInst n v) where
    type HNodesConstraint (NominalInst n v) c = HNodesConstraint v c
    data HWitness (NominalInst n v) c = E_NominalInst_k (HWitness v c)
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (E_NominalInst_k w) = hLiftConstraint w

instance HFunctor v => HFunctor (NominalInst n v) where
    {-# INLINE hmap #-}
    hmap f = nArgs %~ hmap (\w -> _QVarInstances . Lens.mapped %~ f (E_NominalInst_k w))

instance HFoldable v => HFoldable (NominalInst n v) where
    {-# INLINE hfoldMap #-}
    hfoldMap f =
        hfoldMap (\w -> foldMap (f (E_NominalInst_k w)) . (^. _QVarInstances)) . (^. nArgs)

instance HTraversable v => HTraversable (NominalInst n v) where
    {-# INLINE hsequence #-}
    hsequence (NominalInst n v) =
        htraverse (const (_QVarInstances (traverse runContainedH))) v
        <&> NominalInst n

instance
    ( Eq nomId
    , ZipMatch varTypes
    , HTraversable varTypes
    , HNodesConstraint varTypes ZipMatch
    , HNodesConstraint varTypes OrdQVar
    ) =>
    ZipMatch (NominalInst nomId varTypes) where

    {-# INLINE zipMatch #-}
    zipMatch (NominalInst xId x) (NominalInst yId y)
        | xId /= yId = Nothing
        | otherwise =
            zipMatch x y
            >>= htraverse
                ( Proxy @ZipMatch #*# Proxy @OrdQVar #>
                    \(Pair (QVarInstances c0) (QVarInstances c1)) ->
                    zipMatch (TermMap c0) (TermMap c1)
                    <&> (^. _TermMap)
                    <&> QVarInstances
                )
            <&> NominalInst xId

instance Constraints (ToNom nomId term h) Pretty => Pretty (ToNom nomId term h) where
    pPrintPrec lvl p (ToNom nomId term) =
        (pPrint nomId <> Pretty.text "#") <+> pPrintPrec lvl 11 term
        & maybeParens (p > 10)

class    (Pretty (QVar h), Pretty (outer # h)) => PrettyConstraints outer h
instance (Pretty (QVar h), Pretty (outer # h)) => PrettyConstraints outer h

instance
    ( Pretty nomId
    , HApply varTypes, HFoldable varTypes
    , HNodesConstraint varTypes (PrettyConstraints h)
    ) =>
    Pretty (NominalInst nomId varTypes h) where

    pPrint (NominalInst n vars) =
        pPrint n <>
        joinArgs
        (hfoldMap (Proxy @(PrettyConstraints h) #> mkArgs) vars)
        where
            joinArgs [] = mempty
            joinArgs xs =
                Pretty.text "[" <>
                Pretty.sep (Pretty.punctuate (Pretty.text ",") xs)
                <> Pretty.text "]"
            mkArgs (QVarInstances m) =
                Map.toList m <&>
                \(h, v) ->
                (pPrint h <> Pretty.text ":") <+> pPrint v

instance (RNodes t, HNodes (NomVarTypes t)) => HNodes (LoadedNominalDecl t) where
    type HNodesConstraint (LoadedNominalDecl t) c =
        ( HNodesConstraint (NomVarTypes t) c
        , c t
        , Recursive c
        )
    data HWitness (LoadedNominalDecl t) n where
        E_LoadedNominalDecl_Body :: HRecWitness t n -> HWitness (LoadedNominalDecl t) n
        E_LoadedNominalDecl_NomVarTypes :: HWitness (NomVarTypes t) n -> HWitness (LoadedNominalDecl t) n
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (E_LoadedNominalDecl_Body w) = hLiftConstraint (E_Flip_GTerm w)
    hLiftConstraint (E_LoadedNominalDecl_NomVarTypes w) = hLiftConstraint w

instance
    (Recursively HFunctor typ, HFunctor (NomVarTypes typ)) =>
    HFunctor (LoadedNominalDecl typ) where
    {-# INLINE hmap #-}
    hmap f (LoadedNominalDecl mp mf t) =
        LoadedNominalDecl (onMap mp) (onMap mf)
        (t & Lens.from _Flip %~ hmap (\(E_Flip_GTerm w) -> f (E_LoadedNominalDecl_Body w)))
        where
            onMap = hmap (\w -> _QVarInstances . Lens.mapped %~ f (E_LoadedNominalDecl_NomVarTypes w))

instance
    (Recursively HFoldable typ, HFoldable (NomVarTypes typ)) =>
    HFoldable (LoadedNominalDecl typ) where
    {-# INLINE hfoldMap #-}
    hfoldMap f (LoadedNominalDecl mp mf t) =
        onMap mp <> onMap mf <>
        hfoldMap (\(E_Flip_GTerm w) -> f (E_LoadedNominalDecl_Body w)) (_Flip # t)
        where
            onMap = hfoldMap (\w -> foldMap (f (E_LoadedNominalDecl_NomVarTypes w)) . (^. _QVarInstances))

instance
    (RTraversable typ, HTraversable (NomVarTypes typ)) =>
    HTraversable (LoadedNominalDecl typ) where
    {-# INLINE hsequence #-}
    hsequence (LoadedNominalDecl p f t) =
        LoadedNominalDecl
        <$> onMap p
        <*> onMap f
        <*> Lens.from _Flip hsequence t
        where
            onMap = htraverse (const ((_QVarInstances . traverse) runContainedH))

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
        case htraverse (const (^? _GMono)) x of
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
    , HTraversable (NomVarTypes typ)
    , HNodesConstraint (NomVarTypes typ) (Unify m)
    , HasScheme (NomVarTypes typ) m typ
    ) =>
    Tree Pure (NominalDecl typ) ->
    m (Tree (LoadedNominalDecl typ) (UVarOf m))
loadNominalDecl (Pure (NominalDecl params (Scheme foralls typ))) =
    do
        paramsL <- htraverse (Proxy @(Unify m) #> makeQVarInstances) params
        forallsL <- htraverse (Proxy @(Unify m) #> makeQVarInstances) foralls
        wrapM
            (Proxy @(HasScheme (NomVarTypes typ) m) #>>
                loadBody paramsL forallsL
            ) typ
            <&> LoadedNominalDecl paramsL forallsL

class MonadNominals nomId typ m where
    getNominalDecl :: nomId -> m (Tree (LoadedNominalDecl typ) (UVarOf m))

class HasNominalInst nomId typ where
    nominalInst :: Prism' (Tree typ h) (Tree (NominalInst nomId (NomVarTypes typ)) h)

{-# INLINE lookupParams #-}
lookupParams ::
    forall m varTypes.
    ( Applicative m
    , HTraversable varTypes
    , HNodesConstraint varTypes (Unify m)
    ) =>
    Tree varTypes (QVarInstances (UVarOf m)) ->
    m (Tree varTypes (QVarInstances (UVarOf m)))
lookupParams =
    htraverse (Proxy @(Unify m) #> (_QVarInstances . traverse) lookupParam)
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
    , HTraversable (NomVarTypes (TypeOf expr))
    , HNodesConstraint (NomVarTypes (TypeOf expr)) (Unify m)
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
                        htraverse_
                        ( Proxy @(Unify m) #>
                            traverse_ (instantiateForAll USkolem) . (^. _QVarInstances)
                        ) foralls
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
    , HTraversable (NomVarTypes (TypeOf expr))
    , HNodesConstraint (NomVarTypes (TypeOf expr)) (Unify m)
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
