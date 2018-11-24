{-# LANGUAGE NoImplicitPrelude, TypeFamilies, ConstraintKinds #-}
{-# OPTIONS -fno-warn-orphans #-} -- Arbitrary instances
module AST.Arbitrary
    ( ArbitraryWithContext(..)
    , ArbitraryWithContextOf
    ) where

import           AST.Ann
import           Test.QuickCheck (Arbitrary(..), Gen)

import           Prelude.Compat hiding (any)

-- Useful for ASTs
class Arbitrary a => ArbitraryWithContext a where
    type Context a
    arbitraryCtx :: Context a -> Gen a

type ArbitraryWithContextOf c a = (ArbitraryWithContext a, Context a ~ c)

instance (Arbitrary a, Arbitrary v) => Arbitrary (Ann a v) where
    arbitrary = Ann <$> arbitrary <*> arbitrary

instance (Arbitrary a, ArbitraryWithContext v) => ArbitraryWithContext (Ann a v) where
    type Context (Ann a v) = Context v
    arbitraryCtx ctx = Ann <$> arbitrary <*> arbitraryCtx ctx
