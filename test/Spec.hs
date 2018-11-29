{-# LANGUAGE TypeFamilies, UndecidableInstances, UndecidableSuperClasses, FlexibleContexts #-}

import GHC.Exts (Constraint)

data T = T

type family F t (c :: * -> Constraint) :: Constraint
type instance F T c = c T

class F t C => C t where

t :: C T => t
t = undefined
