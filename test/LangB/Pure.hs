-- | Pure combinators for LangB

module LangB.Pure
    ( module LangB.Pure
    , module LangB
    ) where

import AST
import AST.Term.App
import AST.Term.Lam
import AST.Term.Let
import AST.Term.Row
import AST.Term.Var
import AST.Term.Nominal
import Control.Lens.Operators
import LangB
import TypeLang.Pure

import Prelude

bVar :: String -> Tree Pure LangB
bVar = (&# BVar) . Var . Name

lam :: String -> (Tree Pure LangB -> Tree Pure LangB) -> Tree Pure LangB
lam v mk = bVar v & mk & Lam (Name v) &# BLam

bLet ::
    String -> Tree Pure LangB -> (Tree Pure LangB -> Tree Pure LangB) -> Tree Pure LangB
bLet v val body = Let (Name v) val (body (bVar v)) &# BLet

infixl 9 $$
($$) :: Tree Pure LangB -> Tree Pure LangB -> Tree Pure LangB
x $$ y = App x y &# BApp

recExtend :: [(String, Tree Pure LangB)] -> Tree Pure LangB -> Tree Pure LangB
recExtend fields rest = foldr (fmap (&# BRecExtend) . uncurry (RowExtend . Name)) rest fields

closedRec :: [(String, Tree Pure LangB)] -> Tree Pure LangB
closedRec fields = recExtend fields (MkPure BRecEmpty)

getField :: Tree Pure LangB -> String -> Tree Pure LangB
getField w k = Name k &# BGetField w

toNom :: String -> Tree Pure LangB -> Tree Pure LangB
toNom name = (&# BToNom) . ToNom (Name name)
