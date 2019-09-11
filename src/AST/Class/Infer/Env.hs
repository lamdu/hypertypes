module AST.Class.Infer.Env
    ( LocalScopeType(..)
    ) where

-- | @LocalScopeType var scheme m@ represents that @m@ maintains a scope mapping variables of type @var@ to type schemes of type @scheme@
class LocalScopeType var scheme m where
    -- | Add a variable type into an action's scope
    localScopeType :: var -> scheme -> m a -> m a
