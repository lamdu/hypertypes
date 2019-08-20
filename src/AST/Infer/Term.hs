{-# LANGUAGE TemplateHaskell, FlexibleContexts, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}

module AST.Infer.Term
    ( ITerm(..), iVal, iRes, iAnn
    , iAnnotations
    ) where

import AST
-- import AST.Class
-- import AST.Class.Foldable
import AST.Class.Infer
import AST.Class.Recursive
-- import AST.Class.Traversable
-- import AST.Combinator.Flip (Flip(..), _Flip)
import Control.Lens (Traversal, makeLenses)
-- import Control.Lens.Operators
import Data.Constraint
-- import Data.Functor.Product.PolyKinds (Product(..))
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
data ITerm a v e = ITerm
    { _iAnn :: a
    , _iRes :: !(Tree (InferOf (RunKnot e)) v)
    , _iVal :: Node e (ITerm a v)
    }
makeLenses ''ITerm

-- instance KNodes (Flip (ITerm a) e) where

-- instance
--     Inferrable e =>
--     KFunctor (Flip (ITerm a) e) where

-- instance
--     Inferrable e =>
--     KFoldable (Flip (ITerm a) e) where

-- instance
--     Inferrable e =>
--     KTraversable (Flip (ITerm a) e) where

--     {-# INLINE sequenceK #-}
--     sequenceK =
--         withDict (traversableInferOf (Proxy @e)) $
--         withDict (inferrableRecursive (Proxy @e)) $
--         _Flip $
--         \(ITerm a r x) ->
--         ITerm a
--         <$> traverseK runContainedK r
--         <*> traverseKWith (Proxy @Inferrable) (from _Flip sequenceK) x

iAnnotations ::
    forall e a b v.
    RTraversable e =>
    Traversal
    (Tree (ITerm a v) e)
    (Tree (ITerm b v) e)
    a b
iAnnotations f (ITerm pl r x) =
    withDict (recursiveKTraversable (Proxy @e)) $
    ITerm
    <$> f pl
    <*> pure r
    <*> traverseKWith (Proxy @RTraversable) (iAnnotations f) x

deriving instance (Show a, Show (Tree e (ITerm a v)), Show (Tree (InferOf e) v)) => Show (Tree (ITerm a v) e)
