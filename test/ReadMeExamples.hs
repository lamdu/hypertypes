{-# LANGUAGE OverloadedStrings #-}

module ReadMeExamples where

import AST
import Data.Text

data Expr k
    = Var Text
    | App (k # Expr) (k # Expr)
    | Lam Text (k # Typ) (k # Expr)

data Typ k
    = IntT
    | FuncT (k # Typ) (k # Typ)

exprA :: Tree Pure Expr
exprA =
    Pure
    ( Lam "x"
        (Pure IntT)
        (Pure (Var "x"))
    )

exprB :: Tree Pure Expr
exprB =
    Pure
    ( Lam "x"
        (Pure (FuncT (Pure IntT) (Pure IntT)))
        (Pure (Var "x"))
    )
