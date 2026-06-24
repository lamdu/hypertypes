-- | Traits of inference monads.
module Hyper.Infer.Env
    ( LocalScopeType (..)
    ) where

-- | @LocalScopeType var scheme m@ represents that
-- @m@ maintains a scope mapping variables of type @var@
-- to type schemes of type @scheme@.
--
-- Used by the 'Hyper.Infer.Class.Infer' instances
-- of 'Hyper.Syntax.Lam.Lam' and 'Hyper.Syntax.Let.Let'.
class LocalScopeType var scheme m where
    -- | Add a variable type into an action's scope
    localScopeType :: var -> scheme -> m a -> m a
