{-# LANGUAGE OverloadedStrings, TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module ReadMeExamples where

import Hyper
import Hyper.Diff
import Data.Text
import Generics.Constraints (makeDerivings)
import GHC.Generics (Generic)

import Prelude

data Expr k
    = Var Text
    | App (k # Expr) (k # Expr)
    | Lam Text (k # Typ) (k # Expr)
    deriving Generic

data Typ k
    = IntT
    | FuncT (k # Typ) (k # Typ)
    deriving Generic

makeDerivings [''Eq, ''Ord, ''Show] [''Expr, ''Typ]
makeKTraversableAndBases ''Expr
makeKTraversableAndBases ''Typ
makeZipMatch ''Expr
makeZipMatch ''Typ
makeKHasPlain [''Expr, ''Typ]

instance RNodes Expr
instance RNodes Typ
instance (c Expr, c Typ) => Recursively c Expr
instance c Typ => Recursively c Typ
instance RTraversable Expr
instance RTraversable Typ

verboseExpr :: Tree Pure Expr
verboseExpr = Pure (Lam "x" (Pure IntT) (Pure (Var "x")))

exprA, exprB :: KPlain Expr
exprA = LamP "x" IntTP (VarP "x")
exprB = LamP "x" (FuncTP IntTP IntTP) (VarP "x")

d :: Tree DiffP Expr
d = diffP exprA exprB

formatDiff :: (Show a, Show b) => w -> a -> b -> String
formatDiff _ x y = "- " <> show x <> "\n+ " <> show y <> "\n"
