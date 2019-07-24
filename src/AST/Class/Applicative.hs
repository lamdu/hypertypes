{-# LANGUAGE NoImplicitPrelude, FlexibleInstances, UndecidableInstances #-}

module AST.Class.Applicative
    ( KApplicative
    ) where

import AST.Class.Apply (KApply)
import AST.Class.Pointed (KPointed)

class    (KPointed k, KApply k) => KApplicative k
instance (KPointed k, KApply k) => KApplicative k
