-- | Functors as Knots
{-# LANGUAGE TemplateHaskell, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving #-}
module AST.Knot.Functor
    ( ToKnot(..), _ToKnot
    ) where

import AST.Class (KNodes(..), KFunctor)
import AST.Class.Combinators (mapKWith)
import AST.Class.Monad (KMonad(..))
import AST.Class.Recursive (Recursively(..), RecursiveDict)
import AST.Combinator.ANode (ANode(..))
import AST.Combinator.Compose
import AST.Knot (Tree, Node)
import AST.TH.Apply (makeKApplicativeBases)
import AST.TH.Traversable (makeKTraversableAndFoldable)
import Control.DeepSeq (NFData)
import Control.Lens (Iso, iso)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

newtype ToKnot f k = MkToKnot (f (Node k (ToKnot f)))
    deriving stock Generic

_ToKnot ::
    Iso (Tree (ToKnot f0) k0)
        (Tree (ToKnot f1) k1)
        (f0 (Tree k0 (ToKnot f0)))
        (f1 (Tree k1 (ToKnot f1)))
_ToKnot = iso (\(MkToKnot x) -> x) MkToKnot

instance KNodes (ToKnot f) where
    type NodeTypesOf (ToKnot f) = ANode (ToKnot f)

makeKApplicativeBases ''ToKnot
makeKTraversableAndFoldable ''ToKnot

instance Monad f => KMonad (ToKnot f) where
    joinK x =
        withDict (r x) $
        x ^. _Compose . _ToKnot
        >>= (^. _Compose . _ToKnot)
        <&> mapKWith (Proxy @'[Recursively KFunctor]) joinK . getCompose
        & MkToKnot
        where
            r :: Recursively KFunctor l => Tree k l -> RecursiveDict l KFunctor
            r _ = recursive

instance c (ToKnot f) => Recursively c (ToKnot f)

type InToKnot f k = f (Node k (ToKnot f))
deriving instance Eq     (InToKnot f k) => Eq     (ToKnot f k)
deriving instance Ord    (InToKnot f k) => Ord    (ToKnot f k)
deriving instance Show   (InToKnot f k) => Show   (ToKnot f k)
instance Binary (InToKnot f k) => Binary (ToKnot f k)
instance NFData (InToKnot f k) => NFData (ToKnot f k)
