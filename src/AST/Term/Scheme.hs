{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, InstanceSigs, FlexibleContexts, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances #-}

module AST.Term.Scheme
    ( Scheme(..), sForAlls, sTyp
    , Vars(..), _Vars
    , HasChild(..), CanInstantiate
    ) where

import           AST.Class.Children (Children(..), ChildrenConstraint)
import           AST.Class.Children.TH (makeChildren)
import           AST.Class.Instantiate (Instantiate(..))
import           AST.Class.Recursive (Recursive, wrapM)
import           AST.Knot (Tree, Tie, RunKnot)
import           AST.Knot.Pure (Pure(..))
import           AST.Unify (Unify(..), HasQuantifiedVar(..), UniVar, newVar, newTerm)
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

class    (Unify m typ, HasChild varTypes typ) => CanInstantiate m varTypes typ
instance (Unify m typ, HasChild varTypes typ) => CanInstantiate m varTypes typ

makeForAlls :: Unify m typ => Tree Vars typ -> m (Tree (ForAlls (UniVar m)) typ)
makeForAlls (Vars xs) =
    traverse makeSkolem xs <&> ForAlls . Map.fromList
    where
        makeSkolem x = newVar binding USkolem <&> (,) x

instantiateBody ::
    (Unify m typ, HasChild varTypes typ) =>
    Tree varTypes (ForAlls (UniVar m)) -> Tree typ (UniVar m) -> m (Tree (UniVar m) typ)
instantiateBody foralls x =
    case x ^? quantifiedVar >>= getForAll of
    Nothing -> newTerm x
    Just r -> pure r
    where
        getForAll v = foralls ^? getChild . _ForAlls . Lens.ix v

instance Children varTypes => Instantiate (Scheme varTypes typ) where
    type SchemeType (Scheme varTypes typ) = typ

    type InstantiateContext (Scheme varTypes typ) m =
        ( Recursive (CanInstantiate m varTypes) typ
        , ChildrenConstraint varTypes (Unify m)
        , Monad m
        )

    instantiate ::
        forall m.
        InstantiateContext (Scheme varTypes typ) m =>
        Tree Pure (Scheme varTypes typ) -> m (Tree (UniVar m) typ)
    instantiate (Pure (Scheme vars typ)) =
        do
            foralls <- children (Proxy :: Proxy (Unify m)) makeForAlls vars
            wrapM (Proxy :: Proxy (CanInstantiate m varTypes)) (instantiateBody foralls) typ
