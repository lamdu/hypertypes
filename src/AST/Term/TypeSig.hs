{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell, TupleSections #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances, MultiParamTypeClasses, TypeOperators #-}
{-# LANGUAGE UndecidableInstances, StandaloneDeriving, ConstraintKinds #-}

module AST.Term.TypeSig
    ( TypeSig(..), tsType, tsTerm
    ) where

import           AST
import           AST.Class.Combinators (And)
import           AST.Class.HasChild (HasChild(..))
import           AST.Infer (Infer(..), InferIn(..), TypeOf, ScopeOf, MonadScopeLevel(..))
import           AST.Term.Scheme (Scheme, schemeToRestrictedType)
import           AST.Unify (Unify, unify, QVarHasInstance)
import           Control.DeepSeq (NFData)
import           Control.Lens (makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint)
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

data TypeSig vars term k = TypeSig
    { _tsTerm :: Tie k term
    , _tsType :: Tree Pure (Scheme vars (TypeOf term))
    } deriving Generic
makeLenses ''TypeSig

makeChildren ''TypeSig

instance RecursiveConstraint (TypeSig vars term) constraint => Recursive constraint (TypeSig vars term)

type Deps vars term k cls = ((cls (Tie k term), cls (Tree Pure (Scheme vars (TypeOf term)))) :: Constraint)

instance Deps vars term k Pretty => Pretty (TypeSig vars term k) where
    pPrintPrec lvl p (TypeSig term typ) =
        pPrintPrec lvl 1 term <+> Pretty.text ":" <+> pPrintPrec lvl 1 typ
        & maybeParens (p > 1)

type instance TypeOf  (TypeSig vars term) = TypeOf  term
type instance ScopeOf (TypeSig vars term) = ScopeOf term

instance
    ( MonadScopeLevel m
    , Infer m term
    , ChildrenWithConstraint vars (Unify m)
    , Recursive (Unify m `And` HasChild vars `And` QVarHasInstance Ord) (TypeOf term)
    ) =>
    Infer m (TypeSig vars term) where

    inferBody (TypeSig x s) =
        do
            (xT, xI) <- runInferIn x
            schemeToRestrictedType s
                >>= unify xT
                <&> (, TypeSig xI s)
        & localLevel

deriving instance Deps vars term k Eq   => Eq   (TypeSig vars term k)
deriving instance Deps vars term k Ord  => Ord  (TypeSig vars term k)
deriving instance Deps vars term k Show => Show (TypeSig vars term k)
instance Deps vars term k Binary => Binary (TypeSig vars term k)
instance Deps vars term k NFData => NFData (TypeSig vars term k)
