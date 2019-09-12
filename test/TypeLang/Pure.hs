{-# LANGUAGE FlexibleContexts #-}
module TypeLang.Pure
    ( module TypeLang.Pure
    , module TypeLang
    ) where

import           AST
import           AST.Term.FuncType
import           AST.Term.Row
import           AST.Term.Scheme
import           AST.Unify
import           AST.Unify.QuantifiedVar
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Data.Map as Map
import           TypeLang

import           Prelude

rowExtends :: Tree Pure Row -> [(Name, Tree Pure Typ)] -> Tree Pure Row
rowExtends =
    foldr extend
    where
        extend (name, typ) rest =
            RowExtend (name) typ rest &# RExtend

record :: [(Name, Tree Pure Typ)] -> Tree Pure Typ
record fields = rowExtends (_Pure # REmpty) fields &# TRec

uniType :: KPlain Typ -> Tree Pure (Scheme Types Typ)
uniType typ =
    _Pure # Scheme
    { _sForAlls = Types (QVars mempty) (QVars mempty)
    , _sTyp = typ ^. kPlain
    }

forAll ::
    (Traversable t, Traversable u) =>
    t Name -> u Name ->
    (t (Tree Pure Typ) -> u (Tree Pure Row) -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
forAll tvs rvs body =
    _Pure #
    Scheme (Types (foralls tvs) (foralls rvs))
    (body (tvs <&> (&# TVar)) (rvs <&> (&# RVar)))
    where
        foralls ::
            ( Foldable f
            , QVar typ ~ Name
            , Monoid (TypeConstraintsOf typ)
            ) =>
            f Name -> Tree QVars typ
        foralls xs =
            xs ^.. Lens.folded <&> (, mempty)
            & Map.fromList & QVars

forAll1 ::
    Name -> (Tree Pure Typ -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
forAll1 t body =
    forAll (Lens.Identity t) (Lens.Const ()) $ \(Lens.Identity tv) _ -> body tv

forAll1r ::
    Name -> (Tree Pure Row -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
forAll1r t body =
    forAll (Lens.Const ()) (Lens.Identity t) $ \_ (Lens.Identity tv) -> body tv

infixr 2 ~>
(~>) :: Tree Pure Typ -> Tree Pure Typ -> Tree Pure Typ
a ~> b = FuncType a b &# TFun
