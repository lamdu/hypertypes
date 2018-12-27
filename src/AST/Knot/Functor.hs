-- | Functors as Knots
{-# LANGUAGE TemplateHaskell, TypeFamilies, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving #-}
module AST.Knot.Functor
    ( ToKnot(..), _ToKnot
    ) where

import AST.Class.Recursive.TH (makeChildrenRecursive)
import AST.Knot (Tie)
import Control.Lens (makePrisms)
import Data.Binary

newtype ToKnot f k = ToKnot { getToKnot :: f (Tie k (ToKnot f)) }

makePrisms ''ToKnot

type InToKnot f k = f (Tie k (ToKnot f))
deriving instance Eq     (InToKnot f k) => Eq     (ToKnot f k)
deriving instance Ord    (InToKnot f k) => Ord    (ToKnot f k)
deriving instance Show   (InToKnot f k) => Show   (ToKnot f k)
deriving instance Binary (InToKnot f k) => Binary (ToKnot f k)

makeChildrenRecursive [''ToKnot]
