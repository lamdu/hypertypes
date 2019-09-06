-- | Functors as Knots
{-# LANGUAGE TemplateHaskell, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving, GADTs #-}
module AST.Knot.Functor
    ( F(..), _F, KWitness(..)
    ) where

import AST.Class.Nodes (KNodes(..), (#>))
import AST.Class.Functor (KFunctor(..))
import AST.Class.Monad (KMonad(..))
import AST.Class.Recursive (Recursive(..), RNodes, RFunctor, RFoldable, RTraversable)
import AST.Combinator.Compose
import AST.Knot (Tree, type (#))
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.TH.Traversable (makeKTraversableApplyAndBases)
import Control.Lens (Iso, iso, mapped)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

-- | Lift a 'Functor', or type constructor of kind @Type -> Type@ to a 'AST.Knot.Knot'.
--
-- * @F Maybe@ can be used to encode structures with missing values
-- * @F (Either Text)@ can be used to encode results of parsing where structure components
--   may fail to parse.
newtype F f k = F (f (k # F f))
    deriving stock Generic

-- | An 'Iso' from 'F' to its content.
--
-- Using `_F` rather than the 'F' data constructor is recommended,
-- because it helps the type inference know that @F f@ is parameterized with a 'AST.Knot.Knot'.
_F ::
    Iso (Tree (F f0) k0)
        (Tree (F f1) k1)
        (f0 (Tree k0 (F f0)))
        (f1 (Tree k1 (F f1)))
_F = iso (\(F x) -> x) F

makeCommonInstances [''F]
makeKTraversableApplyAndBases ''F

instance Monad f => KMonad (F f) where
    joinK =
        ( _F %~
            ( >>=
                ( mapped %~ t . (^. _Compose)
                ) . (^. _Compose . _F)
            )
        ) . (^. _Compose)
        where
            t ::
                forall p.
                RFunctor p =>
                Tree p (Compose (F f) (F f)) ->
                Tree p (F f)
            t =
                withDict (recurse (Proxy @(RFunctor p))) $
                mapK (Proxy @RFunctor #> joinK)

instance RNodes (F f)
instance Functor f => RFunctor (F f)
instance Foldable f => RFoldable (F f)
instance Traversable f => RTraversable (F f)
