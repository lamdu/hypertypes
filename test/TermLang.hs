{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies #-}

module TermLang where

import AST
import AST.Scope
import AST.TH

data Term v f
    = ELam (Scope Term v f)
    | EVar v
    | EApp (Node f (Term v)) (Node f (Term v))
    | ELit Int

deriving instance
    ( Show v
    , Show (Node f (Term v))
    , Show (Node f (Term (Maybe v)))
    ) =>
    Show (Term v f)

makeChildren [''Term]
