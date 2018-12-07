{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, KindSignatures, TypeFamilies #-}

module AST.Term.Map
    ( TermMap(..)
    ) where

import           AST
import           AST.Class.ZipMatch
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map

import           Prelude.Compat

newtype TermMap k expr f =
    -- TODO: Make th-abstraction support type synonyms and use ``Node
    TermMap (Map k (f (expr f)))
makeChildren [''TermMap]

instance Eq k => ZipMatch (TermMap k expr) where
    zipMatch _ f (TermMap x) (TermMap y)
        | Map.size x /= Map.size y = Nothing
        | otherwise =
            zipMatchList (Map.toList x) (Map.toList y)
            <&> traverse . Lens._2 %%~ uncurry f
            <&> Lens.mapped %~ TermMap . Map.fromAscList

zipMatchList :: Eq k => [(k, a)] -> [(k, b)] -> Maybe [(k, (a, b))]
zipMatchList [] [] = Just []
zipMatchList ((k0, v0) : xs) ((k1, v1) : ys)
    | k0 == k1 =
        zipMatchList xs ys <&> ((k0, (v0, v1)) :)
zipMatchList _ _ = Nothing
