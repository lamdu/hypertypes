-- TODO: Better name?
-- TODO: The usage of NoConstraint is not elegant..

{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, ScopedTypeVariables, FlexibleContexts #-}
{-# LANGUAGE TypeOperators, LambdaCase #-}

module AST.Term.Scheme.Load
    ( LoadedScheme(..), lTerm, lVars
    , loadScheme
    , instantiate
    ) where

import AST.Class.Children (Children(..), ChildrenWithConstraint)
import AST.Class.Combinators (And, NoConstraint, HasChildrenConstraint, proxyNoConstraint)
import AST.Class.HasChild (HasChild(..))
import AST.Class.Recursive (Recursive, wrapM)
import AST.Knot (Tree, RunKnot)
import AST.Knot.Pure (Pure(..))
import AST.Term.Scheme (Scheme(..), SchemeVars, _SchemeVars, makeSchemeVars)
import AST.Unify (Unify(..), UVar, HasQuantifiedVar(..), newTerm)
import AST.Unify.Binding (Binding(..))
import AST.Unify.Generalize (Generalized(..), GTerm(..), _GMono, instantiateWith)
import AST.Unify.Term (UTerm(..))
import Control.Lens (makeLenses, ix)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- A scheme where different instantiations share the scheme's monomorphic part
-- (their unification is O(1) as it is the same shared unification term).

data LoadedScheme varTypes typ v = LoadedScheme
    { _lTerm :: Generalized typ v
    , _lVars :: Tree varTypes (SchemeVars (RunKnot v))
    }
makeLenses ''LoadedScheme

loadBody ::
    ( Unify m typ
    , HasChild varTypes typ
    , ChildrenConstraint typ NoConstraint
    ) =>
    Tree varTypes (SchemeVars (UVar m)) ->
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
        getForAll v = foralls ^? getChild . _SchemeVars . ix v

loadScheme ::
    forall m varTypes typ.
    ( Monad m
    , ChildrenWithConstraint varTypes (Unify m)
    , Recursive (Unify m `And` HasChild varTypes `And` HasChildrenConstraint NoConstraint) typ
    ) =>
    Tree Pure (Scheme varTypes typ) ->
    m (Tree (LoadedScheme varTypes typ) (UVar m))
loadScheme (Pure (Scheme vars typ)) =
    do
        foralls <- children (Proxy :: Proxy (Unify m)) makeSchemeVars vars
        wrapM (Proxy :: Proxy (Unify m `And` HasChild varTypes `And` HasChildrenConstraint NoConstraint))
            (loadBody foralls) typ
            <&> (`LoadedScheme` foralls) . Generalized

instantiate ::
    forall m varTypes typ.
    ( Recursive (Unify m) typ
    , ChildrenWithConstraint varTypes (Unify m)
    ) =>
    Tree (LoadedScheme varTypes typ) (UVar m) ->
    m (Tree (UVar m) typ, Tree varTypes (SchemeVars (UVar m)))
instantiate (LoadedScheme gterm vars) =
    instantiateWith (children (Proxy :: Proxy (Unify m)) ((_SchemeVars . traverse) f) vars) gterm
    where
        f v =
            lookupVar binding v
            >>=
            \case
            UVar r -> pure r
            _ -> error "unexpected state at instantiate's forall"
