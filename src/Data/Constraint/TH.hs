{-# LANGUAGE TemplateHaskellQuotes #-}

module Data.Constraint.TH
    ( defaultDict
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint (Dict(..))
import           Language.Haskell.TH

import           Prelude.Compat

defaultDict :: Name -> DecsQ
defaultDict name =
    reify name
    >>=
    \case
    (VarI _ typ _) -> parseType typ <&> uncurry (makeDefaultDict name typ)
    _ -> fail "defaultDict expects a method name"

parseType :: Type -> Q (Int, Cxt)
parseType (ConT d `AppT` t)
    | d == ''Dict = pure (0, [t])
    | otherwise = fail "defaultDict: method does not result with dict"
parseType (ArrowT `AppT` _ `AppT` t) = parseType t <&> Lens._1 %~ (+1)
parseType _ = fail "defaultDict: unsupported method type"

makeDefaultDict :: Name -> Type -> Int -> Cxt -> [Dec]
makeDefaultDict name t numProxies c =
    [ PragmaD (InlineP name Inline FunLike AllPhases)
    , DefaultSigD name (ForallT [] c t)
    , FunD name [Clause (replicate numProxies WildP) (NormalB (ConE 'Dict)) []]
    ]
