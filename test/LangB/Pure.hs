-- | Pure combinators for LangB

module LangB.Pure
    ( module LangB.Pure
    , module LangB
    ) where

import AST
import AST.Term.Apply
import AST.Term.Lam
import AST.Term.Let
import AST.Term.Row
import AST.Term.Var
import Control.Lens.Operators
import LangB
import TypeLang.Pure

bVar :: String -> Tree Pure LangB
bVar = Pure . BVar . Var . Name

lam :: String -> (Tree Pure LangB -> Tree Pure LangB) -> Tree Pure LangB
lam v mk = bVar v & mk & Lam (Name v) & BLam & Pure

bLet ::
    String -> Tree Pure LangB -> (Tree Pure LangB -> Tree Pure LangB) -> Tree Pure LangB
bLet v val body = Let (Name v) val (body (bVar v)) & BLet & Pure

infixl 9 $$
($$) :: Tree Pure LangB -> Tree Pure LangB -> Tree Pure LangB
x $$ y = Apply x y & BApp & Pure

bLit :: Int -> Tree Pure LangB
bLit = Pure . BLit

recExtend :: [(String, Tree Pure LangB)] -> Tree Pure LangB -> Tree Pure LangB
recExtend fields rest = foldr (fmap (Pure . BRecExtend) . uncurry (RowExtend . Name)) rest fields

closedRec :: [(String, Tree Pure LangB)] -> Tree Pure LangB
closedRec fields = recExtend fields (Pure BRecEmpty)

getField :: Tree Pure LangB -> String -> Tree Pure LangB
getField w k = Name k & BGetField w & Pure
