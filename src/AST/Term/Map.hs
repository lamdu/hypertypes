{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, KindSignatures, TypeFamilies, StandaloneDeriving, UndecidableInstances, DeriveGeneric #-}

module AST.Term.Map
    ( TermMap(..), _TermMap
    ) where

import           AST (Node, ChildrenRecursive, makeChildren)
import           AST.Class.ZipMatch (ZipMatch(..))
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import           GHC.Generics (Generic)

import           Prelude.Compat

newtype TermMap k expr f = TermMap (Map k (Node f expr))
    deriving Generic

deriving instance (Eq   k, Eq   (Node f expr)) => Eq   (TermMap k expr f)
deriving instance (Ord  k, Ord  (Node f expr)) => Ord  (TermMap k expr f)
deriving instance (Show k, Show (Node f expr)) => Show (TermMap k expr f)
instance (Binary k, Binary (Node f expr)) => Binary (TermMap k expr f)
instance (NFData k, NFData (Node f expr)) => NFData (TermMap k expr f)

Lens.makePrisms ''TermMap
makeChildren [''TermMap]

instance ChildrenRecursive expr => ChildrenRecursive (TermMap k expr)

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
