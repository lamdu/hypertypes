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
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..))
import           Data.Constraint
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Hyper
import           Hyper.Class.Has (HasChild(..))
import           Hyper.Class.Recursive
import           Hyper.Infer
import           Hyper.Recurse
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Hyper.Unify
import           Hyper.Unify.Generalize
import           Hyper.Unify.Lookup (semiPruneLookup)
import           Hyper.Unify.New (newTerm)
import           Hyper.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..), OrdQVar)
import           Hyper.Unify.Term (UTerm(..), uBody)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A type scheme representing a polymorphic type.
data Scheme varTypes typ h = Scheme
    { _sForAlls :: Tree varTypes QVars
    , _sTyp :: h # typ
    } deriving Generic

newtype QVars typ = QVars
    (Map (QVar (GetHyperType typ)) (TypeConstraintsOf (GetHyperType typ)))
    deriving stock Generic

newtype QVarInstances h typ = QVarInstances (Map (QVar (GetHyperType typ)) (h typ))
    deriving stock Generic

Lens.makeLenses ''Scheme
Lens.makePrisms ''QVars
Lens.makePrisms ''QVarInstances
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
    (Pretty (Tree varTypes QVars), Pretty (h # typ)) =>
    Pretty (Scheme varTypes typ h) where

    pPrintPrec lvl p (Scheme forAlls typ) =
        pPrintPrec lvl 0 forAlls <+>
        pPrintPrec lvl 0 typ
        & maybeParens (p > 0)

instance
    (Pretty (TypeConstraintsOf typ), Pretty (QVar typ)) =>
    Pretty (Tree QVars typ) where

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

type instance InferOf (Scheme v t) = HFlip GTerm t

class UnifyGen m t => MonadInstantiate m t where
    localInstantiations ::
        Tree (QVarInstances (UVarOf m)) t ->
        m a ->
        m a
    lookupQVar :: QVar t -> m (Tree (UVarOf m) t)

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
    Tree t (InferChild m h) ->
    m (Tree t h, Tree (InferOf t) (UVarOf m))
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
    Tree QVars typ -> m (Tree (QVarInstances (UVarOf m)) typ)
makeQVarInstances (QVars foralls) =
    traverse (newVar binding . USkolem) foralls <&> QVarInstances

{-# INLINE loadBody #-}
loadBody ::
    ( UnifyGen m typ
    , HasChild varTypes typ
    , Ord (QVar typ)
    ) =>
    Tree varTypes (QVarInstances (UVarOf m)) ->
    Tree typ (GTerm (UVarOf m)) ->
    m (Tree (GTerm (UVarOf m)) typ)
loadBody foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Just r -> GPoly r & pure
    Nothing ->
        case htraverse (const (^? _GMono)) x of
        Just xm -> newTerm xm <&> GMono
        Nothing -> GBody x & pure
    where
        getForAll v = foralls ^? getChild . _QVarInstances . Lens.ix v

class
    (UnifyGen m t, HasChild varTypes t, Ord (QVar t)) =>
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
    recurse =
        hasSchemeRecursive (Proxy @varTypes) (Proxy @m) . p
        where
            p :: Proxy (HasScheme varTypes m t) -> Proxy t
            p _ = Proxy

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
    Tree Pure (Scheme varTypes typ) ->
    m (Tree (GTerm (UVarOf m)) typ)
loadScheme (Pure (Scheme vars typ)) =
    do
        foralls <- htraverse (Proxy @(UnifyGen m) #> makeQVarInstances) vars
        wrapM (Proxy @(HasScheme varTypes m) #>> loadBody foralls) typ

saveH ::
    forall typ varTypes m.
    (Monad m, HasScheme varTypes m typ) =>
    Tree (GTerm (UVarOf m)) typ ->
    StateT (Tree varTypes QVars, [m ()]) m (Tree Pure typ)
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
            Lens._1 . getChild %=
                (\v -> v & _QVars . Lens.at r ?~ l :: Tree QVars typ)
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
    Tree (GTerm (UVarOf m)) typ ->
    m (Tree Pure (Scheme varTypes typ))
saveScheme x =
    do
        (t, (v, recover)) <-
            runStateT (saveH x)
            ( hpure (Proxy @OrdQVar #> QVars mempty)
            , []
            )
        _Pure # Scheme v t <$ sequence_ recover
