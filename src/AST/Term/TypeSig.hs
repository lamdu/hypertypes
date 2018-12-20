{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, StandaloneDeriving, ScopedTypeVariables, TupleSections, ConstraintKinds #-}

module AST.Term.TypeSig
    ( TypeSig(..), tsType, tsTerm
    ) where

import           AST
import           AST.Class.Infer
import           AST.Class.Recursive.TH (makeChildrenRecursive)
import           AST.Unify
import           Control.DeepSeq (NFData)
import           Control.Lens.Operators
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Constraint
import           GHC.Generics (Generic)

import           Prelude.Compat

data TypeSig tknot term k = TypeSig
    { _tsType :: Tree tknot (TypeAST term)
    , _tsTerm :: Tie k term
    } deriving Generic
Lens.makeLenses ''TypeSig

makeChildrenRecursive [''TypeSig]

instance RecursiveConstraint (TypeSig tknot term) constraint => Recursive constraint (TypeSig tknot term)

type Deps tknot term k cls = ((cls (Tie k term), cls (Tree tknot (TypeAST term))) :: Constraint)

deriving instance Deps tknot term k Eq   => Eq   (TypeSig tknot term k)
deriving instance Deps tknot term k Ord  => Ord  (TypeSig tknot term k)
deriving instance Deps tknot term k Show => Show (TypeSig tknot term k)
instance Deps tknot term k Binary => Binary (TypeSig tknot term k)
instance Deps tknot term k NFData => NFData (TypeSig tknot term k)

type instance TypeAST (TypeSig tknot term) = TypeAST term

instance Infer m term => Infer m (TypeSig Pure term) where
    infer (TypeSig s x) =
        withDict (recursive :: Dict (RecursiveConstraint (TypeAST term) (Unify m))) $
        do
            r <- inferNode x
            unfreeze s
                >>= unify (r ^. nodeType)
                <&> (, TypeSig s r)
