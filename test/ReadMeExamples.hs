{-# LANGUAGE OverloadedStrings, TemplateHaskell, UndecidableInstances, FlexibleInstances #-}

module ReadMeExamples where

import Data.Text
import GHC.Generics (Generic)
import Generics.Constraints (makeDerivings)
import Hyper
import Hyper.Diff

import Prelude

data Expr h
    = Var Text
    | App (h # Expr) (h # Expr)
    | Lam Text (h # Typ) (h # Expr)
    deriving Generic

data Typ h
    = IntT
    | FuncT (h # Typ) (h # Typ)
    deriving Generic

makeDerivings [''Eq, ''Ord, ''Show] [''Expr, ''Typ]
makeHTraversableAndBases ''Expr
makeHTraversableAndBases ''Typ
makeZipMatch ''Expr
makeZipMatch ''Typ
makeHasHPlain [''Expr, ''Typ]

instance RNodes Expr
instance RNodes Typ
instance (c Expr, c Typ) => Recursively c Expr
instance c Typ => Recursively c Typ
instance RTraversable Expr
instance RTraversable Typ

verboseExpr :: Tree Pure Expr
verboseExpr = Pure (Lam "x" (Pure IntT) (Pure (Var "x")))

exprA, exprB :: HPlain Expr
exprA = LamP "x" IntTP (VarP "x")
exprB = LamP "x" (FuncTP IntTP IntTP) (VarP "x")

d :: Tree DiffP Expr
d = diffP exprA exprB

formatDiff :: (Show a, Show b) => w -> a -> b -> String
formatDiff _ x y = "- " <> show x <> "\n+ " <> show y <> "\n"
