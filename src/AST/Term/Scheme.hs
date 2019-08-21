{-# LANGUAGE TemplateHaskell, FlexibleContexts, DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

module AST.Term.Scheme
    ( Scheme(..), sForAlls, sTyp
    , QVars(..), _QVars
    , HasScheme(..), loadScheme, saveScheme
    , MonadInstantiate(..), inferType

    , QVarInstances(..), _QVarInstances
    , makeQVarInstances
    ) where

import           AST
import           AST.Class.Has (HasChild(..))
import           AST.Class.Recursive
import           AST.Combinator.ANode (ANode)
import           AST.Combinator.Flip (Flip(..))
import           AST.Infer
import           AST.Unify
import           AST.Unify.Lookup (semiPruneLookup)
import           AST.Unify.New (newTerm)
import           AST.Unify.Generalize
import           AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..), OrdQVar)
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
import           Generics.OneLiner (Constraints)
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

Lens.makeLenses ''Scheme
Lens.makePrisms ''QVars
makeKTraversableApplyAndBases ''Scheme

instance RNodes t => RNodes (Scheme v t)
instance (KFoldable (Scheme v t), RFoldable t) => RFoldable (Scheme v t)
instance (KFunctor (Scheme v t), RFunctor t) => RFunctor (Scheme v t)
instance (KTraversable (Scheme v t), RTraversable t) => RTraversable (Scheme v t)
instance (c t, Recursive c, TraverseITermWith c t) => TraverseITermWith c (Scheme v t)

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

instance (RTraversable t, Inferrable t) => Inferrable (Scheme v t) where
    type InferOf (Scheme v t) = Flip GTerm t

class Unify m t => MonadInstantiate m t where
    localInstantiations ::
        Tree (QVarInstances (UVarOf m)) t ->
        m a ->
        m a
    lookupQVar :: QVar t -> m (Tree (UVarOf m) t)

instance
    ( Monad m
    , HasInferredValue typ
    , Unify m typ
    , KTraversable varTypes
    , NodesConstraint varTypes (MonadInstantiate m)
    , RTraversable typ
    , Infer m typ
    ) =>
    Infer m (Scheme varTypes typ) where

    {-# INLINE inferBody #-}
    inferBody (Scheme vars typ) =
        do
            foralls <- traverseKWith (Proxy @(MonadInstantiate m)) makeQVarInstances vars
            let withForalls =
                    foldMapKWith (Proxy @(MonadInstantiate m)) ((:[]) . localInstantiations) foralls
                    & foldl (.) id
            InferredChild typI typR <- inferChild typ & withForalls
            generalize (typR ^. inferredValue)
                <&> InferRes (Scheme vars typI) . MkFlip

inferType ::
    ( InferOf t ~ ANode t
    , KTraversable t
    , NodesConstraint t HasInferredValue
    , Unify m t
    , MonadInstantiate m t
    ) =>
    Tree t (InferChild m k) -> m (InferRes (UVarOf m) k t)
inferType x =
    case x ^? quantifiedVar of
    Just q -> lookupQVar q <&> InferRes (quantifiedVar # q) . MkANode
    Nothing ->
        do
            xI <- traverseK inferChild x
            mapKWith (Proxy @HasInferredValue) (^. inType . inferredValue) xI
                & newTerm
                <&> InferRes (mapK (^. inRep) xI) . MkANode

{-# INLINE makeQVarInstances #-}
makeQVarInstances ::
    Unify m typ =>
    Tree QVars typ -> m (Tree (QVarInstances (UVarOf m)) typ)
makeQVarInstances (QVars foralls) =
    traverse (newVar binding . USkolem) foralls <&> QVarInstances

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

class
    (Unify m t, HasChild varTypes t, Ord (QVar t)) =>
    HasScheme varTypes m t where

    hasSchemeRecursive ::
        Proxy varTypes -> Proxy m -> Proxy t ->
        Dict (NodesConstraint t (HasScheme varTypes m))
    {-# INLINE hasSchemeRecursive #-}
    default hasSchemeRecursive ::
        NodesConstraint t (HasScheme varTypes m) =>
        Proxy varTypes -> Proxy m -> Proxy t ->
        Dict (NodesConstraint t (HasScheme varTypes m))
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
    , KTraversable varTypes
    , NodesConstraint varTypes (Unify m)
    , HasScheme varTypes m typ
    ) =>
    Tree Pure (Scheme varTypes typ) ->
    m (Tree (GTerm (UVarOf m)) typ)
loadScheme (MkPure (Scheme vars typ)) =
    do
        foralls <- traverseKWith (Proxy @(Unify m)) makeQVarInstances vars
        wrapM (Proxy @(HasScheme varTypes m)) (loadBody foralls) typ

saveH ::
    forall typ varTypes m.
    (Monad m, HasScheme varTypes m typ) =>
    Tree (GTerm (UVarOf m)) typ ->
    StateT (Tree varTypes QVars, [m ()]) m (Tree Pure typ)
saveH (GBody x) =
    withDict (hasSchemeRecursive (Proxy @varTypes) (Proxy @m) (Proxy @typ)) $
    traverseKWith (Proxy @(HasScheme varTypes m)) saveH x <&> (_Pure #)
saveH (GMono x) =
    unwrapM (Proxy @(HasScheme varTypes m)) f x & lift
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
    ( NodesConstraint varTypes OrdQVar
    , KPointed varTypes
    , HasScheme varTypes m typ
    ) =>
    Tree (GTerm (UVarOf m)) typ ->
    m (Tree Pure (Scheme varTypes typ))
saveScheme x =
    do
        (t, (v, recover)) <-
            runStateT (saveH x)
            ( pureKWith (Proxy @OrdQVar) (QVars mempty)
            , []
            )
        _Pure # Scheme v t <$ sequence_ recover

deriving instance Constraints (Scheme v t k) Eq   => Eq   (Scheme v t k)
deriving instance Constraints (Scheme v t k) Ord  => Ord  (Scheme v t k)
deriving instance Constraints (Scheme v t k) Show => Show (Scheme v t k)
instance Constraints (Scheme v t k) Binary => Binary (Scheme v t k)
instance Constraints (Scheme v t k) NFData => NFData (Scheme v t k)

deriving instance Constraints (QVars t) Eq   => Eq   (QVars t)
deriving instance Constraints (QVars t) Ord  => Ord  (QVars t)
deriving instance Constraints (QVars t) Show => Show (QVars t)
instance Constraints (QVars t) Binary => Binary (QVars t)
instance Constraints (QVars t) NFData => NFData (QVars t)

deriving instance Constraints (QVarInstances k t) Eq   => Eq   (QVarInstances k t)
deriving instance Constraints (QVarInstances k t) Ord  => Ord  (QVarInstances k t)
deriving instance Constraints (QVarInstances k t) Show => Show (QVarInstances k t)
instance Constraints (QVarInstances k t) Binary => Binary (QVarInstances k t)
instance Constraints (QVarInstances k t) NFData => NFData (QVarInstances k t)
