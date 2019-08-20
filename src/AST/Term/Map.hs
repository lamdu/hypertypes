{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances #-}

module AST.Term.Map
    ( TermMap(..), _TermMap
    ) where

import           AST
import           AST.Class.ZipMatch (ZipMatch(..))
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Dict(..))
import           Data.Functor.Product.PolyKinds (Product(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Generics.OneLiner (Constraints)
import           GHC.Generics (Generic)

import           Prelude.Compat

newtype TermMap k expr f = TermMap (Map k (Node f expr))
    deriving stock Generic

instance KNodes (TermMap k e) where
    type NodesConstraint (TermMap k e) c = c e
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = Dict

Lens.makePrisms ''TermMap
makeKTraversableAndBases ''TermMap

instance Eq k => ZipMatch (TermMap k expr) where
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

deriving instance Constraints (TermMap k e f) Eq   => Eq   (TermMap k e f)
deriving instance Constraints (TermMap k e f) Ord  => Ord  (TermMap k e f)
deriving instance Constraints (TermMap k e f) Show => Show (TermMap k e f)
instance Constraints (TermMap k e f) Binary => Binary (TermMap k e f)
instance Constraints (TermMap k e f) NFData => NFData (TermMap k e f)
