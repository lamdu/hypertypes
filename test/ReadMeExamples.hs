{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module ReadMeExamples where

import Data.Text (Text)
import GHC.Generics (Generic1)
import Generics.Constraints (makeDerivings)
import Hyper
import Hyper.Class.ZipMatch (ZipMatch)
import Hyper.Diff (DiffP, diffP)
import Hyper.Syntax (App, TypedLam, Var)

import Prelude

data Expr h
    = EVar Text
    | EApp (h :# Expr) (h :# Expr)
    | ELam Text (h :# Typ) (h :# Expr)
    deriving (Generic)

data Typ h
    = TInt
    | TFunc (h :# Typ) (h :# Typ)
    deriving (Generic)

makeDerivings [''Eq, ''Ord, ''Show] [''Expr, ''Typ]
makeHTraversableAndBases ''Expr
makeHTraversableAndBases ''Typ
makeZipMatch ''Expr
makeZipMatch ''Typ

instance RNodes Expr
instance RNodes Typ
instance (c Expr, c Typ) => Recursively c Expr
instance c Typ => Recursively c Typ
instance RTraversable Expr
instance RTraversable Typ

data RExpr h
    = RVar (Var Text RExpr h)
    | RApp (App RExpr h)
    | RLam (TypedLam Text Typ RExpr h)
    deriving
        ( Generic
        , Generic1
        , HNodes
        , HFunctor
        , HFoldable
        , HTraversable
        , ZipMatch
        , RNodes
        , RTraversable
        )

instance (c RExpr, c Typ) => Recursively c RExpr

makeHasHPlain [''Expr, ''Typ, ''RExpr]

verboseExpr :: Pure # Expr
verboseExpr = Pure (ELam "x" (Pure TInt) (Pure (EVar "x")))

exprA, exprB :: HPlain RExpr
exprA = RLamP "x" TIntP (RVarP "x")
exprB = RLamP "x" (TFuncP TIntP TIntP) (RVarP "x")

d :: DiffP # RExpr
d = diffP exprA exprB

formatDiff :: (Show a, Show b) => w -> a -> b -> String
formatDiff _ x y = "- " <> show x <> "\n+ " <> show y <> "\n"
