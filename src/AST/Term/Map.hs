{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, StandaloneDeriving, DataKinds #-}
{-# LANGUAGE UndecidableInstances, DeriveGeneric, TypeFamilies, DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ConstraintKinds #-}

module AST.Term.Map
    ( TermMap(..), _TermMap
    ) where

import           AST
import           AST.Combinator.ANode (ANode)
import           AST.Class.ZipMatch (ZipMatch(..))
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           Data.Functor.Product (Product(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           GHC.Generics (Generic)

import           Prelude.Compat

newtype TermMap k expr f = TermMap (Map k (Node f expr))
    deriving stock Generic

instance KNodes (TermMap k e) where
    type NodeTypesOf (TermMap k e) = ANode e

Lens.makePrisms ''TermMap
makeKTraversableAndBases ''TermMap

instance RecursiveContext (TermMap k expr) constraint => Recursively constraint (TermMap k expr)

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

type Deps c k e f = ((c k, c (Node f e)) :: Constraint)
deriving instance Deps Eq   k e f => Eq   (TermMap k e f)
deriving instance Deps Ord  k e f => Ord  (TermMap k e f)
deriving instance Deps Show k e f => Show (TermMap k e f)
instance Deps Binary k e f => Binary (TermMap k e f)
instance Deps NFData k e f => NFData (TermMap k e f)
