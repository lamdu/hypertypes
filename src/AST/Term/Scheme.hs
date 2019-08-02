{-# LANGUAGE TemplateHaskell, GeneralizedNewtypeDeriving, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, UndecidableInstances #-}

module AST.Term.Scheme
    ( Scheme(..), sForAlls, sTyp
    , QVars(..), _QVars
    , schemeToRestrictedType
    , loadScheme, saveScheme

    , QVarInstances(..), _QVarInstances
    , makeQVarInstances
    ) where

import           AST
import           AST.Class.Has (HasChild(..))
import           AST.Class.Recursive
import           AST.Combinator.ANode (ANode)
import           AST.Unify
import           AST.Unify.Lookup (semiPruneLookup)
import           AST.Unify.New (newTerm)
import           AST.Unify.Generalize (GTerm(..), _GMono)
import           AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..), QVarHasInstance)
import           AST.Unify.Term (UTerm(..), uBody)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..))
import           Data.Binary (Binary)
import           Data.Constraint
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A type scheme representing a polymorphic type.
data Scheme varTypes typ k = Scheme
    { _sForAlls :: Tree varTypes QVars
    , _sTyp :: Node k typ
    } deriving Generic

newtype QVars typ = QVars
    (Map (QVar (RunKnot typ)) (TypeConstraintsOf (RunKnot typ)))
    deriving stock Generic

instance KNodes (Scheme v t) where
    type NodeTypesOf (Scheme v t) = ANode t

Lens.makeLenses ''Scheme
Lens.makePrisms ''QVars
makeKTraversableAndBases ''Scheme

instance (c (Scheme v t), Recursively c t) => Recursively c (Scheme v t)

instance
    ( Ord (QVar (RunKnot typ))
    , Semigroup (TypeConstraintsOf (RunKnot typ))
    ) =>
    Semigroup (QVars typ) where
    QVars m <> QVars n = QVars (Map.unionWith (<>) m n)

instance
    ( Ord (QVar (RunKnot typ))
    , Semigroup (TypeConstraintsOf (RunKnot typ))
    ) =>
    Monoid (QVars typ) where
    mempty = QVars Map.empty

instance
    (Pretty (Tree varTypes QVars), Pretty (Node k typ)) =>
    Pretty (Scheme varTypes typ k) where

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

type instance Lens.Index (QVars typ) = QVar (RunKnot typ)
type instance Lens.IxValue (QVars typ) = TypeConstraintsOf (RunKnot typ)

instance Ord (QVar (RunKnot typ)) => Lens.Ixed (QVars typ)

instance Ord (QVar (RunKnot typ)) => Lens.At (QVars typ) where
    at k = _QVars . Lens.at k

newtype QVarInstances k typ = QVarInstances (Map (QVar (RunKnot typ)) (k typ))
    deriving stock Generic
Lens.makePrisms ''QVarInstances

{-# INLINE makeQVarInstancesInScope #-}
makeQVarInstancesInScope ::
    Unify m typ =>
    Tree QVars typ -> m (Tree (QVarInstances (UVarOf m)) typ)
makeQVarInstancesInScope (QVars foralls) =
    traverse makeSkolem foralls <&> QVarInstances
    where
        makeSkolem c = scopeConstraints >>= newVar binding . USkolem . (c <>)

{-# INLINE makeQVarInstances #-}
makeQVarInstances ::
    Unify m typ =>
    Tree QVars typ -> m (Tree (QVarInstances (UVarOf m)) typ)
makeQVarInstances (QVars foralls) =
    traverse (newVar binding . USkolem) foralls <&> QVarInstances

{-# INLINE schemeBodyToType #-}
schemeBodyToType ::
    (Unify m typ, HasChild varTypes typ, Ord (QVar typ)) =>
    Tree varTypes (QVarInstances (UVarOf m)) -> Tree typ (UVarOf m) -> m (Tree (UVarOf m) typ)
schemeBodyToType foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Nothing -> newTerm x
    Just r -> pure r
    where
        getForAll v = foralls ^? getChild . _QVarInstances . Lens.ix v

{-# INLINE schemeToRestrictedType #-}
schemeToRestrictedType ::
    forall m varTypes typ.
    ( Monad m
    , KTraversable varTypes
    , NodesConstraint varTypes $ Unify m
    , RLiftConstraints typ '[Unify m, HasChild varTypes, QVarHasInstance Ord]
    ) =>
    Tree Pure (Scheme varTypes typ) -> m (Tree (UVarOf m) typ)
schemeToRestrictedType (MkPure (Scheme vars typ)) =
    do
        foralls <- traverseKWith (Proxy :: Proxy '[Unify m]) makeQVarInstancesInScope vars
        wrapM
            (Proxy :: Proxy '[Unify m, HasChild varTypes, QVarHasInstance Ord])
            Dict (schemeBodyToType foralls) typ

{-# INLINE loadBody #-}
loadBody ::
    ( Unify m typ
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
        case traverseK (^? _GMono) x of
        Just xm -> newTerm xm <&> GMono
        Nothing -> GBody x & pure
    where
        getForAll v = foralls ^? getChild . _QVarInstances . Lens.ix v

-- | Load scheme into unification monad so that different instantiations share
-- the scheme's monomorphic parts -
-- their unification is O(1) as it is the same shared unification term.
{-# INLINE loadScheme #-}
loadScheme ::
    forall m varTypes typ.
    ( Monad m
    , KTraversable varTypes
    , NodesConstraint varTypes $ Unify m
    , RLiftConstraints typ '[Unify m, HasChild varTypes, QVarHasInstance Ord]
    ) =>
    Tree Pure (Scheme varTypes typ) ->
    m (Tree (GTerm (UVarOf m)) typ)
loadScheme (MkPure (Scheme vars typ)) =
    do
        foralls <- traverseKWith (Proxy :: Proxy '[Unify m]) makeQVarInstances vars
        wrapM (Proxy :: Proxy '[Unify m, HasChild varTypes, QVarHasInstance Ord])
            Dict (loadBody foralls) typ

saveH ::
    forall typ varTypes m.
    Monad m =>
    Tree (RecursiveNodes typ) (KDict '[Unify m, HasChild varTypes, QVarHasInstance Ord]) ->
    Tree (GTerm (UVarOf m)) typ ->
    StateT (Tree varTypes QVars, [m ()]) m (Tree Pure typ)
saveH c (GBody x) =
    withDict (c ^. recSelf . _KDict) $
    traverseKRec c saveH x <&> (_Pure #)
saveH c (GMono x) =
    unwrapMWithDict c Dict f x & lift
    where
        f v =
            semiPruneLookup v
            <&>
            \case
            (_, UTerm t) -> t ^. uBody
            (_, UUnbound{}) -> error "saveScheme of non-toplevel scheme!"
            _ -> error "unexpected state at saveScheme of monomorphic part"
saveH c (GPoly x) =
    withDict (c ^. recSelf . _KDict) $
    lookupVar binding x & lift
    >>=
    \case
    USkolem l ->
        do
            r <- scopeConstraints <&> (<> l) >>= newQuantifiedVariable & lift
            Lens._1 . getChild %=
                (\v -> v & _QVars . Lens.at r ?~ l :: Tree QVars typ)
            Lens._2 %= (bindVar binding x (USkolem l) :)
            let result = _Pure . quantifiedVar # r
            UResolved result & bindVar binding x & lift
            pure result
    UResolved v -> pure v
    _ -> error "unexpected state at saveScheme's forall"

saveScheme ::
    ( NodesConstraint varTypes $ QVarHasInstance Ord
    , KPointed varTypes
    , RLiftConstraints typ '[Unify m, HasChild varTypes, QVarHasInstance Ord]
    , Monad m
    ) =>
    Tree (GTerm (UVarOf m)) typ ->
    m (Tree Pure (Scheme varTypes typ))
saveScheme x =
    do
        (t, (v, recover)) <-
            runStateT (saveH rLiftConstraints x)
            ( pureKWithConstraint (Proxy :: Proxy (QVarHasInstance Ord)) (QVars mempty)
            , []
            )
        _Pure # Scheme v t <$ sequence_ recover

type DepsS c v t k = ((c (Tree v QVars), c (Node k t)) :: Constraint)
deriving instance DepsS Eq   v t k => Eq   (Scheme v t k)
deriving instance DepsS Ord  v t k => Ord  (Scheme v t k)
deriving instance DepsS Show v t k => Show (Scheme v t k)
instance DepsS Binary v t k => Binary (Scheme v t k)
instance DepsS NFData v t k => NFData (Scheme v t k)

type DepsF c t = ((c (TypeConstraintsOf t), c (QVar t)) :: Constraint)
deriving instance DepsF Eq   t => Eq   (Tree QVars t)
deriving instance DepsF Ord  t => Ord  (Tree QVars t)
deriving instance DepsF Show t => Show (Tree QVars t)
instance DepsF Binary t => Binary (Tree QVars t)
instance DepsF NFData t => NFData (Tree QVars t)

type DepsQ c k t = ((c (QVar (RunKnot t)), c (k t)) :: Constraint)
deriving instance DepsQ Eq   k t => Eq   (QVarInstances k t)
deriving instance DepsQ Ord  k t => Ord  (QVarInstances k t)
deriving instance DepsQ Show k t => Show (QVarInstances k t)
instance DepsQ Binary k t => Binary (QVarInstances k t)
instance DepsQ NFData k t => NFData (QVarInstances k t)
