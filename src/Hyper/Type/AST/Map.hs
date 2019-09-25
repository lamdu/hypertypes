{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances #-}

module Hyper.Type.AST.Map
    ( TermMap(..), _TermMap, HWitness(..)
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Functor.Product.PolyKinds (Product(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           GHC.Generics (Generic)
import           Hyper
import           Hyper.Class.ZipMatch (ZipMatch(..))
import           Hyper.TH.Internal.Instances (makeCommonInstances)

import           Prelude.Compat

-- | A mapping of keys to terms.
--
-- Apart from the data type, a 'ZipMatch' instance is also provided.
newtype TermMap h expr f = TermMap (Map h (f # expr))
    deriving stock Generic

Lens.makePrisms ''TermMap
makeCommonInstances [''TermMap]
makeHTraversableApplyAndBases ''TermMap

instance Eq h => ZipMatch (TermMap h expr) where
    {-# INLINE zipMatch #-}
    zipMatch (TermMap x) (TermMap y)
        | Map.size x /= Map.size y = Nothing
        | otherwise =
            zipMatchList (Map.toList x) (Map.toList y)
            <&> traverse . Lens._2 %~ uncurry Pair
            <&> TermMap . Map.fromAscList

{-# INLINE zipMatchList #-}
zipMatchList :: Eq k => [(k, a)] -> [(k, b)] -> Maybe [(k, (a, b))]
zipMatchList [] [] = Just []
zipMatchList ((k0, v0) : xs) ((k1, v1) : ys)
    | k0 == k1 =
        zipMatchList xs ys <&> ((k0, (v0, v1)) :)
zipMatchList _ _ = Nothing
