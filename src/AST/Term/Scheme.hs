{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, DataKinds #-}
{-# LANGUAGE ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances, DeriveGeneric, StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}

module AST.Term.Scheme
    ( Scheme(..), sForAlls, sTyp
    , ForAlls(..), _ForAlls
    ) where

import           Algebra.Lattice (JoinSemiLattice(..))
import           AST.Class.Children (Children(..), ChildrenWithConstraint)
import           AST.Class.Children.TH (makeChildren)
import           AST.Class.Combinators (And)
import           AST.Class.HasChild (HasChild(..))
import           AST.Class.Instantiate (Instantiate(..), SchemeType)
import           AST.Class.Recursive (Recursive, wrapM)
import           AST.Knot (Tree, Tie, RunKnot)
import           AST.Knot.Pure (Pure(..))
import           AST.Unify (Unify(..), UVar, newTerm)
import           AST.Unify.Binding (Binding(..))
import           AST.Unify.Constraints (HasTypeConstraints(..), ScopeConstraintsMonad(..))
import           AST.Unify.QuantifiedVar (HasQuantifiedVar(..))
import           AST.Unify.Term (UTerm(..))
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data Scheme varTypes typ k = Scheme
    { _sForAlls :: Tree varTypes ForAlls
    , _sTyp :: Tie k typ
    } deriving Generic

newtype ForAlls typ = ForAlls
    (Map (QVar (RunKnot typ)) (TypeConstraintsOf (RunKnot typ)))
    deriving Generic

type DepsS c v t k = ((c (Tree v ForAlls), c (Tie k t)) :: Constraint)
deriving instance DepsS Eq   v t k => Eq   (Scheme v t k)
deriving instance DepsS Ord  v t k => Ord  (Scheme v t k)
deriving instance DepsS Show v t k => Show (Scheme v t k)
instance DepsS Binary v t k => Binary (Scheme v t k)
instance DepsS NFData v t k => NFData (Scheme v t k)

type DepsF c t = ((c (TypeConstraintsOf t), c (QVar t)) :: Constraint)
deriving instance DepsF Eq   t => Eq   (Tree ForAlls t)
deriving instance DepsF Ord  t => Ord  (Tree ForAlls t)
deriving instance DepsF Show t => Show (Tree ForAlls t)
instance DepsF Binary t => Binary (Tree ForAlls t)
instance DepsF NFData t => NFData (Tree ForAlls t)

instance
    (Pretty (Tree varTypes ForAlls), Pretty (Tie k typ)) =>
    Pretty (Scheme varTypes typ k) where

    pPrintPrec lvl p (Scheme forAlls typ) =
        pPrintPrec lvl 0 forAlls <+>
        pPrintPrec lvl 0 typ
        & maybeParens (p > 0)

instance
    (Pretty (TypeConstraintsOf typ), Pretty (QVar typ)) =>
    Pretty (Tree ForAlls typ) where

    pPrint (ForAlls qvars) =
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
Lens.makePrisms ''ForAlls
makeChildren ''Scheme

newtype Instantiation k typ = Instantiation (Map (QVar (RunKnot typ)) (k typ))
Lens.makePrisms ''Instantiation

makeInstantiation ::
    Unify m typ =>
    Tree ForAlls typ -> m (Tree (Instantiation (UVar m)) typ)
makeInstantiation (ForAlls foralls) =
    traverse makeSkolem foralls <&> Instantiation
    where
        makeSkolem c = scopeConstraints >>= newVar binding . USkolem . (c \/)

instantiateBody ::
    (Unify m typ, HasChild varTypes typ) =>
    Tree varTypes (Instantiation (UVar m)) -> Tree typ (UVar m) -> m (Tree (UVar m) typ)
instantiateBody foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Nothing -> newTerm x
    Just r -> pure r
    where
        getForAll v = foralls ^? getChild . _Instantiation . Lens.ix v

type instance SchemeType (Tree Pure (Scheme varTypes typ)) = typ

instance
    ( Recursive (Unify m) typ
    , Recursive (And (Unify m) (HasChild varTypes)) typ
    , ChildrenWithConstraint varTypes (Unify m)
    ) =>
    Instantiate m (Tree Pure (Scheme varTypes typ)) where

    instantiate (Pure (Scheme vars typ)) =
        do
            foralls <- children (Proxy :: Proxy (Unify m)) makeInstantiation vars
            wrapM (Proxy :: Proxy (And (Unify m) (HasChild varTypes))) (instantiateBody foralls) typ
