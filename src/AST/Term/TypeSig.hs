{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, StandaloneDeriving, ScopedTypeVariables, TupleSections, ConstraintKinds #-}

module AST.Term.TypeSig
    ( TypeSig(..), tsType, tsTerm
    ) where

import           AST
import           AST.Class.Infer
import           AST.Class.Instantiate
import           AST.Class.Recursive.TH (makeChildrenRecursive)
import           AST.Unify
import           Control.DeepSeq (NFData)
import           Control.Lens.Operators
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Constraint
import           GHC.Generics (Generic)

import           Prelude.Compat

data TypeSig typ term k = TypeSig
    { _tsType :: typ
    , _tsTerm :: Tie k term
    } deriving Generic
Lens.makeLenses ''TypeSig

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
    (Infer m term, Instantiate scheme, SchemeType scheme ~ TypeAST term) =>
    Infer m (TypeSig (Tree Pure scheme) term) where

    infer (TypeSig s x) =
        withDict (recursive :: Dict (RecursiveConstraint (TypeAST term) (Unify m))) $
        do
            r <- inferNode x
            instantiate s
                >>= unify (r ^. nodeType)
                <&> (, TypeSig s r)
