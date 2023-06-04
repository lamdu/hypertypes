{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Hyper.Syntax.Map
    ( TermMap (..)
    , _TermMap
    , W_TermMap (..)
    , MorphWitness (..)
    ) where

import qualified Control.Lens as Lens
import qualified Data.Map as Map
import Hyper
import Hyper.Class.ZipMatch (ZipMatch (..))

import Hyper.Internal.Prelude

-- | A mapping of keys to terms.
--
-- Apart from the data type, a 'ZipMatch' instance is also provided.
newtype TermMap h expr f = TermMap (Map h (f :# expr))
    deriving stock (Generic)

makePrisms ''TermMap
makeCommonInstances [''TermMap]
makeHTraversableApplyAndBases ''TermMap
makeHMorph ''TermMap

instance Eq h => ZipMatch (TermMap h expr) where
    {-# INLINE zipMatch #-}
    zipMatch (TermMap x) (TermMap y)
        | Map.size x /= Map.size y = Nothing
        | otherwise =
            zipMatchList (x ^@.. Lens.itraversed) (y ^@.. Lens.itraversed)
                <&> TermMap . Map.fromAscList . (traverse . Lens._2 %~ uncurry (:*:))

{-# INLINE zipMatchList #-}
zipMatchList :: Eq k => [(k, a)] -> [(k, b)] -> Maybe [(k, (a, b))]
zipMatchList [] [] = Just []
zipMatchList ((k0, v0) : xs) ((k1, v1) : ys)
    | k0 == k1 =
        zipMatchList xs ys <&> ((k0, (v0, v1)) :)
zipMatchList _ _ = Nothing
