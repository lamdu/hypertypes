{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, UndecidableInstances #-}

module AST.Class.Applicative
    ( KApplicative
    ) where

import AST.Class (KPointed)
import AST.Class.Apply (KApply)

class    (KPointed k, KApply k) => KApplicative k
instance (KPointed k, KApply k) => KApplicative k
