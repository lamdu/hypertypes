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
import           AST.Class.Instantiate (Instantiate(..), SchemeType)
import           AST.Class.Recursive (Recursive, wrapM)
import           AST.Knot (Tree, Tie, RunKnot)
import           AST.Knot.Pure (Pure(..))
import           AST.Unify (MonadUnify, Unify(..), HasQuantifiedVar(..), UVar, newVar, newTerm, scopeConstraintsForType)
import           AST.Unify.Term (UTerm(..))
import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Proxy (Proxy(..))
import           Data.Map (Map)
import qualified Data.Map as Map

import           Prelude.Compat

data Scheme varTypes typ k = Scheme
    { _sForAlls :: Tree varTypes Vars
    , _sTyp :: Tie k typ
    }

newtype Vars typ = Vars [QVar (RunKnot typ)]

Lens.makeLenses ''Scheme
Lens.makePrisms ''Vars
makeChildren ''Scheme

newtype ForAlls k typ = ForAlls (Map (QVar (RunKnot typ)) (k typ))
Lens.makePrisms ''ForAlls

class HasChild record typ where
    getChild :: Lens' (Tree record k) (Tree k typ)

makeForAlls ::
    forall m typ.
    Unify m typ =>
    Tree Vars typ -> m (Tree (ForAlls (UVar m)) typ)
makeForAlls (Vars xs) =
    traverse makeSkolem xs <&> ForAlls . Map.fromList
    where
        makeSkolem x =
            scopeConstraintsForType (Proxy :: Proxy typ)
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
    ( MonadUnify m
    , Recursive (Unify m) typ
    , Recursive (And (Unify m) (HasChild varTypes)) typ
    , ChildrenWithConstraint varTypes (Unify m)
    ) =>
    Instantiate m (Tree Pure (Scheme varTypes typ)) where

    instantiate (Pure (Scheme vars typ)) =
        do
            foralls <- children (Proxy :: Proxy (Unify m)) makeForAlls vars
            wrapM (Proxy :: Proxy (And (Unify m) (HasChild varTypes))) (instantiateBody foralls) typ
