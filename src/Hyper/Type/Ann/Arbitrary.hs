-- | 'Arbitrary' instance for annotated ASTs, respecting scopes.

{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-} -- Arbitrary instances

module Hyper.Type.Ann.Arbitrary
    ( ArbitraryWithContext(..)
    , ArbitraryWithContextOf
    ) where

import Hyper.Type (type (#))
import Hyper.Type.Ann (Ann(..))
import Test.QuickCheck (Arbitrary(..), Gen)

import Prelude.Compat hiding (any)

-- Useful for ASTs
class Arbitrary a => ArbitraryWithContext a where
    type Context a
    arbitraryCtx :: Context a -> Gen a

type ArbitraryWithContextOf c a = (ArbitraryWithContext a, Context a ~ c)

instance (Arbitrary a, Arbitrary (h # Ann a)) => Arbitrary (Ann a h) where
    arbitrary = Ann <$> arbitrary <*> arbitrary

instance (Arbitrary a, ArbitraryWithContext (h # Ann a)) => ArbitraryWithContext (Ann a h) where
    type Context (Ann a h) = Context (h # Ann a)
    arbitraryCtx ctx = Ann <$> arbitrary <*> arbitraryCtx ctx
