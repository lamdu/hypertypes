-- | Alpha-equality for schemes
{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies, ScopedTypeVariables, TypeOperators #-}
{-# LANGUAGE ConstraintKinds, LambdaCase #-}
module AST.Term.Scheme.AlphaEq
    ( alphaEq
    ) where

import           AST
import           AST.Class.Combinators (And)
import           AST.Class.FromChildren
import           AST.Class.HasChild (HasChild(..))
import           AST.Class.ZipMatch
import           AST.Term.Scheme
import           AST.Unify.QuantifiedVar
import           Control.Applicative (empty)
import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (guard)
import           Control.Monad.State (StateT(..), execStateT)
import           Data.Constraint (withDict)
import           Data.Functor.Identity (Identity(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

-- | For each kind of type variable, a map of variables of this kind
-- to corresponding variables in an alpha-equal type
newtype QVarMap typ = QVarMap (Map (QVar (RunKnot typ)) (QVar (RunKnot typ)))
Lens.makePrisms ''QVarMap

emptyMapping ::
    forall varTypes.
    ( FromChildren varTypes
    , ChildrenConstraint varTypes (HasChild varTypes `And` QVarHasInstance Ord)
    ) =>
    Tree varTypes QVarMap
emptyMapping =
    fromChildren (Proxy :: Proxy (HasChild varTypes `And` QVarHasInstance Ord))
    (Identity (QVarMap mempty))
    & runIdentity

type AlphaEqConstraint varTypes =
    ZipMatch `And` QVarHasInstance Ord `And` HasChild varTypes

alphaEqTypes ::
    forall varTypes typ.
    Recursive (AlphaEqConstraint varTypes) typ =>
    Tree Pure typ ->
    Tree Pure typ ->
    StateT (Tree varTypes QVarMap) Maybe ()
alphaEqTypes (MkPure x) (MkPure y) =
    case (x ^? quantifiedVar, y ^? quantifiedVar) of
    (Just xVar, Just yVar) ->
        Lens.zoom (getQVarMap . _QVarMap . Lens.at xVar) $
        Lens.use id >>=
        \case
        Nothing -> id ?= yVar
        Just oldYVar -> guard (oldYVar == yVar)
    (Nothing, Nothing) ->
        withDict (recursive :: RecursiveDict (AlphaEqConstraint varTypes) typ) $
        zipMatchWith_
        (Proxy :: Proxy (Recursive (AlphaEqConstraint varTypes)))
        alphaEqTypes x y
        & fromMaybe empty
    _ -> empty
    where
        getQVarMap :: Lens' (Tree varTypes QVarMap) (Tree QVarMap typ)
        getQVarMap = getChild

substMap :: (Ord k0, Ord k1) => Map k0 k1 -> Map k0 v -> Maybe (Map k1 v)
substMap s m =
    Map.toList m
    & traverse . Lens._1 %%~ (`Map.lookup` s)
    <&> Map.fromList

alphaEq ::
    forall varTypes typ.
    ( Recursive (AlphaEqConstraint varTypes) typ
    , FromChildren varTypes
    , ChildrenWithConstraint varTypes (HasChild varTypes `And` QVarHasInstance Ord)
    , Eq (Tree varTypes QVars)
    ) =>
    Tree Pure (Scheme varTypes typ) ->
    Tree Pure (Scheme varTypes typ) ->
    Bool
alphaEq (MkPure (Scheme xForAll xTyp)) (MkPure (Scheme yForAll yTyp)) =
    case mVarMapping of
    Nothing -> False
    Just varMapping ->
        children (Proxy :: Proxy (HasChild varTypes `And` QVarHasInstance Ord))
        substForAlls xForAll
        == Just yForAll
        where
            substForAlls ::
                forall child.
                (HasChild varTypes child, Ord (QVar child)) =>
                Tree QVars child -> Maybe (Tree QVars child)
            substForAlls =
                _QVars (substMap (mapping ^. _QVarMap))
                where
                    mapping :: Tree QVarMap child
                    mapping = varMapping ^. getChild
    where
        mVarMapping =
            execStateT (alphaEqTypes xTyp yTyp)
            (emptyMapping :: Tree varTypes QVarMap)
