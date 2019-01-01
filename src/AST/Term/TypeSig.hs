{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, TupleSections #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, StandaloneDeriving, ConstraintKinds #-}

module AST.Term.TypeSig
    ( TypeSig(..), tsType, tsTerm
    ) where

import AST
import AST.Class.Infer (Infer(..), TypeAST, inferNode, nodeType)
import AST.Class.Infer.ScopeLevel (MonadLevel(..))
import AST.Class.Instantiate (Instantiate(..), SchemeType)
import AST.Class.Recursive.TH (makeChildrenRecursive)
import AST.Unify (unify)
import Control.DeepSeq (NFData)
import Control.Lens (makeLenses)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Constraint (Constraint)
import GHC.Generics (Generic)

import Prelude.Compat

data TypeSig typ term k = TypeSig
    { _tsType :: typ
    , _tsTerm :: Tie k term
    } deriving Generic
makeLenses ''TypeSig

makeChildrenRecursive [''TypeSig]

instance RecursiveConstraint (TypeSig typ term) constraint => Recursive constraint (TypeSig typ term)

type Deps typ term k cls = ((cls (Tie k term), cls typ) :: Constraint)

deriving instance Deps typ term k Eq   => Eq   (TypeSig typ term k)
deriving instance Deps typ term k Ord  => Ord  (TypeSig typ term k)
deriving instance Deps typ term k Show => Show (TypeSig typ term k)
instance Deps typ term k Binary => Binary (TypeSig typ term k)
instance Deps typ term k NFData => NFData (TypeSig typ term k)

type instance TypeAST (TypeSig typ term) = TypeAST term

instance
    ( MonadLevel m
    , Infer m term
    , Instantiate m (Tree Pure scheme)
    , SchemeType (Tree Pure scheme) ~ TypeAST term
    ) =>
    Infer m (TypeSig (Tree Pure scheme) term) where

    infer (TypeSig s x) =
        do
            r <- inferNode x
            instantiate s
                >>= unify (r ^. nodeType)
                <&> (, TypeSig s r)
        & localLevel
