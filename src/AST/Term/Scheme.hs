{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module AST.Term.Scheme
    ( Scheme(..), sForAlls, sTyp
    , Vars(..), _Vars
    , HasChild(..)
    ) where

import           AST.Class.Children (Children(..), ChildrenWithConstraint)
import           AST.Class.Children.TH (makeChildren)
import           AST.Class.Combinators (And)
import           AST.Class.HasChild (HasChild(..))
import           AST.Class.Instantiate (Instantiate(..), SchemeType)
import           AST.Class.Recursive (Recursive, wrapM)
import           AST.Knot (Tree, Tie, RunKnot)
import           AST.Knot.Pure (Pure(..))
import           AST.Unify (Unify(..), HasQuantifiedVar(..), UVar, newVar, newTerm)
import           AST.Unify.Term (UTerm(..))
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(..))
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data Scheme varTypes typ k = Scheme
    { _sForAlls :: Tree varTypes Vars
    , _sTyp :: Tie k typ
    }

newtype Vars typ = Vars [QVar (RunKnot typ)]

instance (Pretty (Tree varTypes Vars), Pretty (Tie k typ)) =>
         Pretty (Scheme varTypes typ k) where
    pPrintPrec lvl p (Scheme forAlls typ) =
        pPrintPrec lvl 0 forAlls <+>
        pPrintPrec lvl 0 typ
        & maybeParens (p > 0)

instance Pretty (QVar (RunKnot typ)) => Pretty (Vars typ) where
    pPrint (Vars qVars) =
        qVars <&> pPrint <&> (Pretty.text "∀" <>) <&> (<> Pretty.text ".") & Pretty.hsep

Lens.makeLenses ''Scheme
Lens.makePrisms ''Vars
makeChildren ''Scheme

newtype ForAlls k typ = ForAlls (Map (QVar (RunKnot typ)) (k typ))
Lens.makePrisms ''ForAlls

makeForAlls ::
    forall m typ.
    Unify m typ =>
    Tree Vars typ -> m (Tree (ForAlls (UVar m)) typ)
makeForAlls (Vars xs) =
    traverse makeSkolem xs <&> ForAlls . Map.fromList
    where
        makeSkolem x =
            scopeConstraints (Proxy :: Proxy typ)
            >>= newVar binding . USkolem
            <&> (,) x

instantiateBody ::
    (Unify m typ, HasChild varTypes typ) =>
    Tree varTypes (ForAlls (UVar m)) -> Tree typ (UVar m) -> m (Tree (UVar m) typ)
instantiateBody foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Nothing -> newTerm x
    Just r -> pure r
    where
        getForAll v = foralls ^? getChild . _ForAlls . Lens.ix v

type instance SchemeType (Tree Pure (Scheme varTypes typ)) = typ

instance
    ( Recursive (Unify m) typ
    , Recursive (And (Unify m) (HasChild varTypes)) typ
    , ChildrenWithConstraint varTypes (Unify m)
    ) =>
    Instantiate m (Tree Pure (Scheme varTypes typ)) where

    instantiate (Pure (Scheme vars typ)) =
        do
            foralls <- children (Proxy :: Proxy (Unify m)) makeForAlls vars
            wrapM (Proxy :: Proxy (And (Unify m) (HasChild varTypes))) (instantiateBody foralls) typ
