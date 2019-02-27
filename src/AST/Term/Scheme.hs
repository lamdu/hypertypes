{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, DataKinds #-}
{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric, StandaloneDeriving, FlexibleContexts, LambdaCase #-}
{-# LANGUAGE ConstraintKinds, TypeOperators, GeneralizedNewtypeDeriving #-}

module AST.Term.Scheme
    ( Scheme(..), sForAlls, sTyp
    , QVars(..), _QVars
    , schemeAsType
    , loadScheme, saveScheme

    , QVarInstances(..), _QVarInstances
    , makeQVarInstances
    ) where

import           Algebra.Lattice (JoinSemiLattice(..), BoundedJoinSemiLattice)
import           AST
import           AST.Class.Combinators (And, NoConstraint, HasChildrenConstraint, proxyNoConstraint)
import           AST.Class.FromChildren (FromChildren(..))
import           AST.Class.HasChild (HasChild(..))
import           AST.Class.Recursive (wrapM, unwrapM)
import           AST.Unify
import           AST.Unify.Binding (Binding(..))
import           AST.Unify.Generalize (GTerm(..), _GMono)
import           AST.Unify.Term (UTerm(..), uBody)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.State (StateT(..))
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           Data.Functor.Identity (Identity(..))
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
    , _sTyp :: Tie k typ
    } deriving Generic

newtype QVars typ = QVars
    (Map (QVar (RunKnot typ)) (TypeConstraintsOf (RunKnot typ)))
    deriving (Generic)

instance
    (Pretty (Tree varTypes QVars), Pretty (Tie k typ)) =>
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

Lens.makeLenses ''Scheme
Lens.makePrisms ''QVars
makeChildren ''Scheme

type instance Lens.Index (QVars typ) = QVar (RunKnot typ)
type instance Lens.IxValue (QVars typ) = TypeConstraintsOf (RunKnot typ)

instance Ord (QVar (RunKnot typ)) => Lens.Ixed (QVars typ)

instance Ord (QVar (RunKnot typ)) => Lens.At (QVars typ) where
    at k = _QVars . Lens.at k

newtype QVarInstances k typ = QVarInstances (Map (QVar (RunKnot typ)) (k typ))
    deriving Generic
Lens.makePrisms ''QVarInstances

{-# INLINE makeQVarInstances #-}
makeQVarInstances ::
    Unify m typ =>
    Tree QVars typ -> m (Tree (QVarInstances (UVar m)) typ)
makeQVarInstances (QVars foralls) =
    traverse makeSkolem foralls <&> QVarInstances
    where
        makeSkolem c = scopeConstraints >>= newVar binding . USkolem . (c \/)

{-# INLINE schemeBodyToType #-}
schemeBodyToType ::
    (Unify m typ, HasChild varTypes typ, Ord (QVar typ)) =>
    Tree varTypes (QVarInstances (UVar m)) -> Tree typ (UVar m) -> m (Tree (UVar m) typ)
schemeBodyToType foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Nothing -> newTerm x
    Just r -> pure r
    where
        getForAll v = foralls ^? getChild . _QVarInstances . Lens.ix v

{-# INLINE schemeAsType #-}
schemeAsType ::
    forall m varTypes typ.
    ( Monad m
    , ChildrenWithConstraint varTypes (Unify m)
    , Recursive (Unify m `And` HasChild varTypes `And` QVarHasInstance Ord) typ
    ) =>
    Tree Pure (Scheme varTypes typ) -> m (Tree (UVar m) typ)
schemeAsType (Pure (Scheme vars typ)) =
    do
        foralls <- children (Proxy :: Proxy (Unify m)) makeQVarInstances vars
        wrapM
            (Proxy :: Proxy (Unify m `And` HasChild varTypes `And` QVarHasInstance Ord))
            (schemeBodyToType foralls) typ

{-# INLINE loadBody #-}
loadBody ::
    ( Unify m typ
    , HasChild varTypes typ
    , ChildrenConstraint typ NoConstraint
    , Ord (QVar typ)
    ) =>
    Tree varTypes (QVarInstances (UVar m)) ->
    Tree typ (GTerm (UVar m)) ->
    m (Tree (GTerm (UVar m)) typ)
loadBody foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Just r -> GPoly r & pure
    Nothing ->
        case children proxyNoConstraint (^? _GMono) x of
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
    , ChildrenWithConstraint varTypes (Unify m)
    , Recursive (Unify m `And` HasChild varTypes `And` QVarHasInstance Ord `And` HasChildrenConstraint NoConstraint) typ
    ) =>
    Tree Pure (Scheme varTypes typ) ->
    m (Tree (GTerm (UVar m)) typ)
loadScheme (Pure (Scheme vars typ)) =
    do
        foralls <- children (Proxy :: Proxy (Unify m)) makeQVarInstances vars
        wrapM (Proxy :: Proxy (Unify m `And` HasChild varTypes `And` QVarHasInstance Ord `And` HasChildrenConstraint NoConstraint))
            (loadBody foralls) typ

saveH ::
    forall m varTypes typ.
    Recursive (Unify m `And` HasChild varTypes `And` QVarHasInstance Ord) typ =>
    Tree (GTerm (UVar m)) typ ->
    StateT (Tree varTypes QVars, [m ()]) m (Tree Pure typ)
saveH (GBody x) =
    recursiveChildren
    (Proxy :: Proxy (Unify m `And` HasChild varTypes `And` QVarHasInstance Ord))
    saveH x <&> Pure
saveH (GMono x) =
    unwrapM
    (Proxy :: Proxy (Unify m `And` HasChild varTypes `And` QVarHasInstance Ord))
    f x & lift
    where
        f v =
            lookupVar binding v
            <&>
            \case
            UTerm t -> t ^. uBody
            _ -> error "unexpected state at saveScheme of monomorphic part"
saveH (GPoly x) =
    lookupVar binding x & lift
    >>=
    \case
    USkolem l ->
        do
            r <- scopeConstraints <&> (\/ l) >>= newQuantifiedVariable & lift
            Lens._1 . getChild %=
                (\v -> v & _QVars . Lens.at r ?~ l :: Tree QVars typ)
            Lens._2 %= (bindVar binding x (USkolem l) :)
            let result = quantifiedVar # r & Pure
            UResolved result & bindVar binding x & lift
            pure result
    UResolved v -> pure v
    _ -> error "unexpected state at saveScheme's forall"

saveScheme ::
    ( ChildrenWithConstraint varTypes (QVarHasInstance Ord)
    , FromChildren varTypes
    , Recursive (Unify m `And` HasChild varTypes `And` QVarHasInstance Ord) typ
    ) =>
    Tree (GTerm (UVar m)) typ ->
    m (Tree Pure (Scheme varTypes typ))
saveScheme x =
    do
        (t, (v, recover)) <-
            runStateT (saveH x)
            ( fromChildren (Proxy :: Proxy (QVarHasInstance Ord)) (Identity (QVars mempty))
                & runIdentity
            , []
            )
        Pure (Scheme v t) <$ sequence_ recover

type DepsS c v t k = ((c (Tree v QVars), c (Tie k t)) :: Constraint)
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

deriving instance
    ( Ord (QVar (RunKnot typ))
    , JoinSemiLattice (TypeConstraintsOf (RunKnot typ))
    ) =>
    JoinSemiLattice (QVars typ)
deriving instance
    ( Ord (QVar (RunKnot typ))
    , JoinSemiLattice (TypeConstraintsOf (RunKnot typ))
    ) =>
    BoundedJoinSemiLattice (QVars typ)
