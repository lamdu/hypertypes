{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies #-}

module Lang where

import AST
import AST.TH
import Control.Lens.Operators

data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)

data Term v f
    = ELam v (Node f (Term v))
    | EVar v
    | EApp (Node f (Term v)) (Node f (Term v))
    | ELit Int

deriving instance (Show (f (Typ f)), Show (Row f)) => Show (Typ f)
deriving instance (Show (f (Typ f)), Show (f (Row f))) => Show (Row f)
deriving instance (Show v, Show (Node f (Term v))) => Show (Term v f)

[makeChildren, makeZipMatch] <*> [''Typ, ''Row] & sequenceA <&> concat
makeChildren ''Term -- TODO: makeZipMatch should work too
