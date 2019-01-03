{-# LANGUAGE TypeFamilies #-}
module TypeLang.Pure
    ( module TypeLang.Pure
    , module TypeLang
    ) where

import AST
import AST.Term.FuncType
import AST.Term.Scheme
import Control.Lens.Operators
import TypeLang

intA :: Tree Pure (Scheme Types Typ)
intA = Pure TInt & uniType

tVar :: String -> Tree Pure Typ
tVar = Pure . TVar . Name

uniType :: Tree Pure Typ -> Tree Pure (Scheme Types Typ)
uniType typ =
    Pure Scheme
    { _sForAlls = Types (Vars []) (Vars [])
    , _sTyp = typ
    }

scheme ::
    [String] -> [String] ->
    ([Tree Pure Typ] -> [Tree Pure Typ] -> Tree Pure typ) ->
    Tree Pure (Scheme Types typ)
scheme tvs rowvs body =
    body (tvs <&> tVar) (rowvs <&> tVar)
    & Scheme (Types (Vars (tvs <&> Name)) (Vars (rowvs <&> Name)))
    & Pure

infixr 2 ~>
(~>) :: Tree Pure Typ -> Tree Pure Typ -> Tree Pure Typ
a ~> b = FuncType a b & TFun & Pure
