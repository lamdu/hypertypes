-- | Nominal (named) types declaration, instantiation, construction, and access.

{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, EmptyCase #-}

module Hyper.Type.AST.Nominal
    ( NominalDecl(..), nParams, nScheme, W_NominalDecl(..)
    , NominalInst(..), nId, nArgs
    , ToNom(..), tnId, tnVal, W_ToNom(..)
    , FromNom(..), _FromNom

    , HasNominalInst(..)
    , NomVarTypes
    , MonadNominals(..)
    , LoadedNominalDecl, loadNominalDecl
    ) where

import           Control.Applicative (Alternative(..))
import           Control.Lens (Prism')
import qualified Control.Lens as Lens
import           Control.Monad.Trans.Writer (execWriterT)
import qualified Data.Map as Map
import           Generics.Constraints (Constraints)
import           Hyper
import           Hyper.Class.Context (HContext(..))
import           Hyper.Class.Has (HasChild(..))
import           Hyper.Class.Traversable (ContainedH(..))
import           Hyper.Class.ZipMatch (ZipMatch(..))
import           Hyper.Infer
import           Hyper.Recurse
import           Hyper.Type.AST.FuncType (FuncType(..))
import           Hyper.Type.AST.Map (TermMap(..), _TermMap)
import           Hyper.Type.AST.Scheme
import           Hyper.Unify
import           Hyper.Unify.Generalize (GTerm(..), _GMono, instantiateWith, instantiateForAll)
import           Hyper.Unify.New (newTerm)
import           Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..), OrdQVar)
import           Hyper.Unify.Term (UTerm(..))
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Hyper.Internal.Prelude

type family NomVarTypes (t :: HyperType) :: HyperType

-- | A declaration of a nominal type.
data NominalDecl typ h = NominalDecl
    { _nParams :: NomVarTypes typ # QVars
    , _nScheme :: Scheme (NomVarTypes typ) typ h
    } deriving Generic

-- | An instantiation of a nominal type
data NominalInst nomId varTypes h = NominalInst
    { _nId :: nomId
    , _nArgs :: varTypes # QVarInstances (GetHyperType h)
    } deriving Generic

-- | Nominal data constructor.
--
-- Wrap content with a data constructor
-- (analogues to a data constructor of a Haskell `newtype`'s).
--
-- Introduces the nominal's foralled type variables into the value's scope.
data ToNom nomId term h = ToNom
    { _tnId :: nomId
    , _tnVal :: h :# term
    } deriving Generic

-- | Access the data in a nominally typed value.
--
-- Analogues to a getter of a Haskell `newtype`.
newtype FromNom nomId (term :: HyperType) (h :: AHyperType) = FromNom nomId
    deriving newtype (Eq, Ord, Binary, NFData)
    deriving stock (Show, Generic)

-- | A nominal declaration loaded into scope in an inference monad.
data LoadedNominalDecl typ v = LoadedNominalDecl
    { _lnParams :: NomVarTypes typ # QVarInstances (GetHyperType v)
    , _lnForalls :: NomVarTypes typ # QVarInstances (GetHyperType v)
    , _lnType :: GTerm (GetHyperType v) # typ
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
makeHContext ''ToNom
makeHContext ''FromNom

instance HNodes v => HNodes (NominalInst n v) where
    type HNodesConstraint (NominalInst n v) c = HNodesConstraint v c
    type HWitnessType (NominalInst n v) = HWitnessType v
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (HWitness w) = hLiftConstraint @v (HWitness w)

instance HFunctor v => HFunctor (NominalInst n v) where
    {-# INLINE hmap #-}
    hmap f = nArgs %~ hmap (\(HWitness w) -> _QVarInstances . Lens.mapped %~ f (HWitness w))

instance HFoldable v => HFoldable (NominalInst n v) where
    {-# INLINE hfoldMap #-}
    hfoldMap f =
        hfoldMap (\(HWitness w) -> foldMap (f (HWitness w)) . (^. _QVarInstances)) . (^. nArgs)

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
                    \(QVarInstances c0 :*: QVarInstances c1) ->
                    zipMatch (TermMap c0) (TermMap c1)
                    <&> (^. _TermMap)
                    <&> QVarInstances
                )
            <&> NominalInst xId

instance
    ( HFunctor varTypes
    , HContext varTypes
    , HNodesConstraint varTypes OrdQVar
    ) => HContext (NominalInst nomId varTypes) where
    hcontext (NominalInst n args) =
        hcontext args
        & hmap
            ( Proxy @OrdQVar #>
                \(HFunc c :*: x) ->
                x & _QVarInstances . Lens.imapped %@~
                \k v ->
                HFunc
                ( \newV ->
                    x
                    & _QVarInstances . Lens.at k ?~ newV
                    & c & getConst & NominalInst n
                    & Const
                ) :*: v
            )
        & NominalInst n

instance Constraints (ToNom nomId term h) Pretty => Pretty (ToNom nomId term h) where
    pPrintPrec lvl p (ToNom nomId term) =
        (pPrint nomId <> Pretty.text "#") <+> pPrintPrec lvl 11 term
        & maybeParens (p > 10)

class    (Pretty (QVar h), Pretty (outer :# h)) => PrettyConstraints outer h
instance (Pretty (QVar h), Pretty (outer :# h)) => PrettyConstraints outer h

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

data W_LoadedNominalDecl t n where
    E_LoadedNominalDecl_Body :: HRecWitness t n -> W_LoadedNominalDecl t n
    E_LoadedNominalDecl_NomVarTypes :: HWitness (NomVarTypes t) n -> W_LoadedNominalDecl t n

instance (RNodes t, HNodes (NomVarTypes t)) => HNodes (LoadedNominalDecl t) where
    type HNodesConstraint (LoadedNominalDecl t) c =
        ( HNodesConstraint (NomVarTypes t) c
        , c t
        , Recursive c
        )
    type HWitnessType (LoadedNominalDecl t) = W_LoadedNominalDecl t
    {-# INLINE hLiftConstraint #-}
    hLiftConstraint (HWitness (E_LoadedNominalDecl_Body w)) = hLiftConstraint @(HFlip GTerm _) (HWitness w)
    hLiftConstraint (HWitness (E_LoadedNominalDecl_NomVarTypes w)) = hLiftConstraint w

instance
    (Recursively HFunctor typ, HFunctor (NomVarTypes typ)) =>
    HFunctor (LoadedNominalDecl typ) where
    {-# INLINE hmap #-}
    hmap f (LoadedNominalDecl mp mf t) =
        LoadedNominalDecl (onMap mp) (onMap mf)
        (t & hflipped %~ hmap (\(HWitness w) -> f (HWitness (E_LoadedNominalDecl_Body w))))
        where
            onMap = hmap (\w -> _QVarInstances . Lens.mapped %~ f (HWitness (E_LoadedNominalDecl_NomVarTypes w)))

instance
    (Recursively HFoldable typ, HFoldable (NomVarTypes typ)) =>
    HFoldable (LoadedNominalDecl typ) where
    {-# INLINE hfoldMap #-}
    hfoldMap f (LoadedNominalDecl mp mf t) =
        onMap mp <> onMap mf <>
        hfoldMap (\(HWitness w) -> f (HWitness (E_LoadedNominalDecl_Body w))) (_HFlip # t)
        where
            onMap =
                hfoldMap (\w -> foldMap (f (HWitness (E_LoadedNominalDecl_NomVarTypes w)))
                . (^. _QVarInstances))

instance
    (RTraversable typ, HTraversable (NomVarTypes typ)) =>
    HTraversable (LoadedNominalDecl typ) where
    {-# INLINE hsequence #-}
    hsequence (LoadedNominalDecl p f t) =
        LoadedNominalDecl
        <$> onMap p
        <*> onMap f
        <*> hflipped hsequence t
        where
            onMap = htraverse (const ((_QVarInstances . traverse) runContainedH))

{-# INLINE loadBody #-}
loadBody ::
    ( UnifyGen m typ
    , HasChild varTypes typ
    , Ord (QVar typ)
    ) =>
    varTypes # QVarInstances (UVarOf m) ->
    varTypes # QVarInstances (UVarOf m) ->
    typ # GTerm (UVarOf m) ->
    m (GTerm (UVarOf m) # typ)
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
    Pure # NominalDecl typ ->
    m (LoadedNominalDecl typ # UVarOf m)
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
    getNominalDecl :: nomId -> m (LoadedNominalDecl typ # UVarOf m)

class HasNominalInst nomId typ where
    nominalInst :: Prism' (typ # h) (NominalInst nomId (NomVarTypes typ) # h)

{-# INLINE lookupParams #-}
lookupParams ::
    forall m varTypes.
    ( Applicative m
    , HTraversable varTypes
    , HNodesConstraint varTypes (UnifyGen m)
    ) =>
    varTypes # QVarInstances (UVarOf m) ->
    m (varTypes # QVarInstances (UVarOf m))
lookupParams =
    htraverse (Proxy @(UnifyGen m) #> (_QVarInstances . traverse) lookupParam)
    where
        lookupParam :: forall t. UnifyGen m t => UVarOf m # t -> m (UVarOf m # t)
        lookupParam v =
            lookupVar binding v
            >>=
            \case
            UInstantiated r -> pure r
            USkolem l ->
                -- This is a phantom-type, wasn't instantiated by `instantiate`.
                scopeConstraints (Proxy @t) <&> (<> l) >>= newVar binding . UUnbound
            _ -> error "unexpected state at nominal's parameter"

type instance InferOf (ToNom n e) = NominalInst n (NomVarTypes (TypeOf e))

instance
    ( MonadScopeLevel m
    , MonadNominals nomId (TypeOf expr) m
    , HTraversable (NomVarTypes (TypeOf expr))
    , HNodesConstraint (NomVarTypes (TypeOf expr)) (UnifyGen m)
    , UnifyGen m (TypeOf expr)
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
                        ( Proxy @(UnifyGen m) #>
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
    , HNodesConstraint (NomVarTypes (TypeOf expr)) (UnifyGen m)
    , UnifyGen m (TypeOf expr)
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
