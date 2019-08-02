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

rowExtends :: Tree Pure Row -> [(String, Tree Pure Typ)] -> Tree Pure Row
rowExtends =
    foldr extend
    where
        extend (name, typ) rest =
            _Pure # RExtend (RowExtend (Name name) typ rest)

record :: [(String, Tree Pure Typ)] -> Tree Pure Typ
record fields = _Pure # TRec (rowExtends (_Pure # REmpty) fields)

intA :: Tree Pure (Scheme Types Typ)
intA = _Pure # TInt & uniType

tVar :: String -> Tree Pure Typ
tVar n = _Pure # TVar (Name n)

rVar :: String -> Tree Pure Row
rVar n = _Pure # RVar (Name n)

uniType :: Tree Pure Typ -> Tree Pure (Scheme Types Typ)
uniType typ =
    _Pure # Scheme
    { _sForAlls = Types (QVars mempty) (QVars mempty)
    , _sTyp = typ
    }

forAll ::
    (Traversable t, Traversable u) =>
    t String -> u String ->
    (t (Tree Pure Typ) -> u (Tree Pure Row) -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
forAll tvs rvs body =
    _Pure #
    Scheme (Types (foralls tvs) (foralls rvs))
    (body (tvs <&> tVar) (rvs <&> rVar))
    where
        foralls ::
            ( Foldable f
            , QVar typ ~ Name
            , Monoid (TypeConstraintsOf typ)
            ) =>
            f String -> Tree QVars typ
        foralls xs =
            xs ^.. Lens.folded <&> Name <&> (, mempty)
            & Map.fromList & QVars

forAll1 ::
    String -> (Tree Pure Typ -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
forAll1 t body =
    forAll (Lens.Identity t) (Lens.Const ()) $ \(Lens.Identity tv) _ -> body tv

forAll1r ::
    String -> (Tree Pure Row -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
forAll1r t body =
    forAll (Lens.Const ()) (Lens.Identity t) $ \_ (Lens.Identity tv) -> body tv

infixr 2 ~>
(~>) :: Tree Pure Typ -> Tree Pure Typ -> Tree Pure Typ
a ~> b = _Pure # TFun (FuncType a b)
