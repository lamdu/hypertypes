-- | Type schemes

{-# LANGUAGE TemplateHaskell, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module Hyper.Type.AST.Scheme
    ( Scheme(..), sForAlls, sTyp, W_Scheme(..)
    , QVars(..), _QVars
    , HasScheme(..), loadScheme, saveScheme
    , MonadInstantiate(..), inferType

    , QVarInstances(..), _QVarInstances
    , makeQVarInstances
    ) where

import qualified Control.Lens as Lens
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..))
import qualified Data.Map as Map
import           Hyper
import           Hyper.Class.Optic (HNodeLens(..))
import           Hyper.Infer
import           Hyper.Recurse
import           Hyper.Unify
import           Hyper.Unify.Generalize
import           Hyper.Unify.New (newTerm)
import           Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..), OrdQVar)
import           Hyper.Unify.Term (UTerm(..), uBody)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Hyper.Internal.Prelude

-- | A type scheme representing a polymorphic type.
data Scheme varTypes typ h = Scheme
    { _sForAlls :: varTypes # QVars
    , _sTyp :: h :# typ
    } deriving Generic

newtype QVars typ = QVars
    (Map (QVar (GetHyperType typ)) (TypeConstraintsOf (GetHyperType typ)))
    deriving stock Generic

newtype QVarInstances h typ = QVarInstances (Map (QVar (GetHyperType typ)) (h typ))
    deriving stock Generic

makeLenses ''Scheme
makePrisms ''QVars
makePrisms ''QVarInstances
makeCommonInstances [''Scheme, ''QVars, ''QVarInstances]
makeHTraversableApplyAndBases ''Scheme

instance RNodes t => RNodes (Scheme v t)
instance (c (Scheme v t), Recursively c t) => Recursively c (Scheme v t)
instance (HTraversable (Scheme v t), RTraversable t) => RTraversable (Scheme v t)
instance (RTraversable t, RTraversableInferOf t) => RTraversableInferOf (Scheme v t)

instance
    ( Ord (QVar (GetHyperType typ))
    , Semigroup (TypeConstraintsOf (GetHyperType typ))
    ) =>
    Semigroup (QVars typ) where
    QVars m <> QVars n = QVars (Map.unionWith (<>) m n)

instance
    ( Ord (QVar (GetHyperType typ))
    , Semigroup (TypeConstraintsOf (GetHyperType typ))
    ) =>
    Monoid (QVars typ) where
    mempty = QVars Map.empty

instance
    (Pretty (varTypes # QVars), Pretty (h :# typ)) =>
    Pretty (Scheme varTypes typ h) where

    pPrintPrec lvl p (Scheme forAlls typ)
        | Pretty.isEmpty f = pPrintPrec lvl p typ
        | otherwise = f <+> pPrintPrec lvl 0 typ & maybeParens (p > 0)
        where
            f = pPrintPrec lvl 0 forAlls

instance
    (Pretty (TypeConstraintsOf typ), Pretty (QVar typ)) =>
    Pretty (QVars # typ) where

    pPrint (QVars qvars) =
        Map.toList qvars
        <&> printVar
        <&> (Pretty.text "∀" <>) <&> (<> Pretty.text ".") & Pretty.hsep
        where
            printVar (q, c)
                | cP == mempty = pPrint q
                | otherwise = pPrint q <> Pretty.text "(" <> cP <> Pretty.text ")"
                where
                    cP = pPrint c

type instance Lens.Index (QVars typ) = QVar (GetHyperType typ)
type instance Lens.IxValue (QVars typ) = TypeConstraintsOf (GetHyperType typ)

instance Ord (QVar (GetHyperType typ)) => Lens.Ixed (QVars typ)

instance Ord (QVar (GetHyperType typ)) => Lens.At (QVars typ) where
    at h = _QVars . Lens.at h

type instance InferOf (Scheme _ t) = HFlip GTerm t

class UnifyGen m t => MonadInstantiate m t where
    localInstantiations ::
        QVarInstances (UVarOf m) # t ->
        m a ->
        m a
    lookupQVar :: QVar t -> m (UVarOf m # t)

instance
    ( Monad m
    , HasInferredValue typ
    , UnifyGen m typ
    , HTraversable varTypes
    , HNodesConstraint varTypes (MonadInstantiate m)
    , RTraversable typ
    , Infer m typ
    ) =>
    Infer m (Scheme varTypes typ) where

    {-# INLINE inferBody #-}
    inferBody (Scheme vars typ) =
        do
            foralls <- htraverse (Proxy @(MonadInstantiate m) #> makeQVarInstances) vars
            let withForalls =
                    hfoldMap
                    (Proxy @(MonadInstantiate m) #> (:[]) . localInstantiations)
                    foralls
                    & foldl (.) id
            InferredChild typI typR <- inferChild typ & withForalls
            generalize (typR ^. inferredValue)
                <&> (Scheme vars typI, ) . MkHFlip

inferType ::
    ( InferOf t ~ ANode t
    , HTraversable t
    , HNodesConstraint t HasInferredValue
    , UnifyGen m t
    , MonadInstantiate m t
    ) =>
    t # InferChild m h ->
    m (t # h, InferOf t # UVarOf m)
inferType x =
    case x ^? quantifiedVar of
    Just q -> lookupQVar q <&> (quantifiedVar # q, ) . MkANode
    Nothing ->
        do
            xI <- htraverse (const inferChild) x
            hmap (Proxy @HasInferredValue #> (^. inType . inferredValue)) xI
                & newTerm
                <&> (hmap (const (^. inRep)) xI, ) . MkANode

{-# INLINE makeQVarInstances #-}
makeQVarInstances ::
    Unify m typ =>
    QVars # typ -> m (QVarInstances (UVarOf m) # typ)
makeQVarInstances (QVars foralls) =
    traverse (newVar binding . USkolem) foralls <&> QVarInstances

{-# INLINE loadBody #-}
loadBody ::
    ( UnifyGen m typ
    , HNodeLens varTypes typ
    , Ord (QVar typ)
    ) =>
    varTypes # QVarInstances (UVarOf m) ->
    typ # GTerm (UVarOf m) ->
    m (GTerm (UVarOf m) # typ)
loadBody foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Just r -> GPoly r & pure
    Nothing ->
        case htraverse (const (^? _GMono)) x of
        Just xm -> newTerm xm <&> GMono
        Nothing -> GBody x & pure
    where
        getForAll v = foralls ^? hNodeLens . _QVarInstances . Lens.ix v

class
    (UnifyGen m t, HNodeLens varTypes t, Ord (QVar t)) =>
    HasScheme varTypes m t where

    hasSchemeRecursive ::
        Proxy varTypes -> Proxy m -> Proxy t ->
        Dict (HNodesConstraint t (HasScheme varTypes m))
    {-# INLINE hasSchemeRecursive #-}
    default hasSchemeRecursive ::
        HNodesConstraint t (HasScheme varTypes m) =>
        Proxy varTypes -> Proxy m -> Proxy t ->
        Dict (HNodesConstraint t (HasScheme varTypes m))
    hasSchemeRecursive _ _ _ = Dict

instance Recursive (HasScheme varTypes m) where
    recurse = hasSchemeRecursive (Proxy @varTypes) (Proxy @m) . proxyArgument

-- | Load scheme into unification monad so that different instantiations share
-- the scheme's monomorphic parts -
-- their unification is O(1) as it is the same shared unification term.
{-# INLINE loadScheme #-}
loadScheme ::
    forall m varTypes typ.
    ( Monad m
    , HTraversable varTypes
    , HNodesConstraint varTypes (UnifyGen m)
    , HasScheme varTypes m typ
    ) =>
    Pure # Scheme varTypes typ ->
    m (GTerm (UVarOf m) # typ)
loadScheme (Pure (Scheme vars typ)) =
    do
        foralls <- htraverse (Proxy @(UnifyGen m) #> makeQVarInstances) vars
        wrapM (Proxy @(HasScheme varTypes m) #>> loadBody foralls) typ

saveH ::
    forall typ varTypes m.
    (Monad m, HasScheme varTypes m typ) =>
    GTerm (UVarOf m) # typ ->
    StateT (varTypes # QVars, [m ()]) m (Pure # typ)
saveH (GBody x) =
    withDict (hasSchemeRecursive (Proxy @varTypes) (Proxy @m) (Proxy @typ)) $
    htraverse (Proxy @(HasScheme varTypes m) #> saveH) x <&> (_Pure #)
saveH (GMono x) =
    unwrapM (Proxy @(HasScheme varTypes m) #>> f) x & lift
    where
        f v =
            semiPruneLookup v
            <&>
            \case
            (_, UTerm t) -> t ^. uBody
            (_, UUnbound{}) -> error "saveScheme of non-toplevel scheme!"
            _ -> error "unexpected state at saveScheme of monomorphic part"
saveH (GPoly x) =
    lookupVar binding x & lift
    >>=
    \case
    USkolem l ->
        do
            r <-
                scopeConstraints (Proxy @typ) <&> (<> l)
                >>= newQuantifiedVariable & lift
            Lens._1 . hNodeLens %=
                (\v -> v & _QVars . Lens.at r ?~ generalizeConstraints l :: QVars # typ)
            Lens._2 %= (bindVar binding x (USkolem l) :)
            let result = _Pure . quantifiedVar # r
            UResolved result & bindVar binding x & lift
            pure result
    UResolved v -> pure v
    _ -> error "unexpected state at saveScheme's forall"

saveScheme ::
    ( HNodesConstraint varTypes OrdQVar
    , HPointed varTypes
    , HasScheme varTypes m typ
    ) =>
    GTerm (UVarOf m) # typ ->
    m (Pure # Scheme varTypes typ)
saveScheme x =
    do
        (t, (v, recover)) <-
            runStateT (saveH x)
            ( hpure (Proxy @OrdQVar #> QVars mempty)
            , []
            )
        _Pure # Scheme v t <$ sequence_ recover
