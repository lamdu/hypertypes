-- | Syntax trees with pruned branches - aka ASTs with holes.
--
-- `PruneTerm ast` adds holes as an option in the AST recursively.

{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE DataKinds, MultiParamTypeClasses, FlexibleInstances, DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies, TupleSections #-}

module AST.Trans.Prune
    ( PruneTerm(..), PruneKnot(..)
    ) where

import           AST
import           AST.Class.Combinators (NoConstraint, proxyNoConstraint)
import           AST.Infer
import           AST.Unify (newUnbound)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens (makePrisms)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)

import           Prelude.Compat

data PruneTerm expr k =
    Pruned | Unpruned (Tree expr (PruneKnot (RunKnot k)))
    deriving Generic

newtype PruneKnot k expr =
    MkPruneKnot (Tree k (PruneTerm (RunKnot expr)))
    deriving stock Generic

makePrisms ''PruneTerm
makePrisms ''PruneKnot

class c (t k) => TransConstraint c (t :: (Knot -> *) -> Knot -> *) k
instance c (t k) => TransConstraint c t k

instance Children k => Children (PruneKnot k) where
    type ChildrenConstraint (PruneKnot k) c = ChildrenConstraint k (TransConstraint c PruneKnot)
    children p f (MkPruneKnot x) =
        children (liftP p) (_Unpruned f) x <&> MkPruneKnot
        where
            liftP :: Proxy c -> Proxy (TransConstraint c PruneKnot)
            liftP _ = Proxy

instance Children expr => Children (PruneTerm expr) where
    type ChildrenConstraint (PruneTerm expr) c = ChildrenConstraint expr (TransConstraint c PruneTerm)
    children _ _ Pruned = pure Pruned
    children p f (Unpruned x) =
        children (liftP p) (_MkPruneKnot f) x <&> Unpruned
        where
            liftP :: Proxy c -> Proxy (TransConstraint c PruneTerm)
            liftP _ = Proxy

type instance TypeOf  (PruneTerm t) = TypeOf  t
type instance ScopeOf (PruneTerm t) = ScopeOf t

instance (ChildrenWithConstraint t NoConstraint, Infer m t) => Infer m (PruneTerm t) where
    inferBody Pruned = newUnbound <&> (, Pruned)
    inferBody (Unpruned x) =
        overChildren proxyNoConstraint
        (\(MkPruneKnot (InferIn i)) -> i <&> Lens._2 %~ MkPruneKnot & InferIn)
        x & inferBody
        <&> Lens._2 %~ Unpruned

instance (Children e, RecursiveConstraint (PruneTerm e) c) => Recursive c (PruneTerm e)
instance (Children k, RecursiveConstraint (PruneKnot k) c) => Recursive c (PruneKnot k)

deriving instance Eq   (Tree k (PruneTerm (RunKnot e))) => Eq   (PruneKnot k e)
deriving instance Eq   (Tree e (PruneKnot (RunKnot k))) => Eq   (PruneTerm e k)
deriving instance Ord  (Tree k (PruneTerm (RunKnot e))) => Ord  (PruneKnot k e)
deriving instance Ord  (Tree e (PruneKnot (RunKnot k))) => Ord  (PruneTerm e k)
deriving instance Show (Tree k (PruneTerm (RunKnot e))) => Show (PruneKnot k e)
deriving instance Show (Tree e (PruneKnot (RunKnot k))) => Show (PruneTerm e k)
instance Binary (Tree k (PruneTerm (RunKnot e))) => Binary (PruneKnot k e)
instance Binary (Tree e (PruneKnot (RunKnot k))) => Binary (PruneTerm e k)
instance NFData (Tree k (PruneTerm (RunKnot e))) => NFData (PruneKnot k e)
instance NFData (Tree e (PruneKnot (RunKnot k))) => NFData (PruneTerm e k)
