{-# LANGUAGE TypeFamilies, TupleSections, FlexibleContexts #-}
module TypeLang.Pure
    ( module TypeLang.Pure
    , module TypeLang
    ) where

import           AST
import           AST.Term.FuncType
import           AST.Term.Row
import           AST.Term.Scheme
import           AST.Unify
import           Algebra.Lattice
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Data.Map as Map
import           TypeLang

rowExtends :: Tree Pure Row -> [(String, Tree Pure Typ)] -> Tree Pure Row
rowExtends =
    foldr extend
    where
        extend (name, typ) = Pure . RExtend . RowExtend (Name name) typ

record :: [(String, Tree Pure Typ)] -> Tree Pure Typ
record = Pure . TRec . rowExtends (Pure REmpty)

intA :: Tree Pure (Scheme Types Typ)
intA = Pure TInt & uniType

tVar :: String -> Tree Pure Typ
tVar = Pure . TVar . Name

rVar :: String -> Tree Pure Row
rVar = Pure . RVar . Name

uniType :: Tree Pure Typ -> Tree Pure (Scheme Types Typ)
uniType typ =
    Pure Scheme
    { _sForAlls = Types (QVars mempty) (QVars mempty)
    , _sTyp = typ
    }

forAll ::
    (Traversable t, Traversable u) =>
    t String -> u String ->
    (t (Tree Pure Typ) -> u (Tree Pure Row) -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
forAll tvs rvs body =
    body (tvs <&> tVar) (rvs <&> rVar)
    & Scheme (Types (foralls tvs) (foralls rvs))
    & Pure
    where
        foralls ::
            ( Foldable f
            , QVar typ ~ Name
            , BoundedJoinSemiLattice (TypeConstraintsOf typ)
            ) =>
            f String -> Tree QVars typ
        foralls xs =
            xs ^.. Lens.folded <&> Name <&> (, bottom)
            & Map.fromList & QVars

forAll1 ::
    String -> (Tree Pure Typ -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
forAll1 t body =
    forAll (Lens.Identity t) (Lens.Const ()) $ \(Lens.Identity tv) _ -> body tv

infixr 2 ~>
(~>) :: Tree Pure Typ -> Tree Pure Typ -> Tree Pure Typ
a ~> b = FuncType a b & TFun & Pure
