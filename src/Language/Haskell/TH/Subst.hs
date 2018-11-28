{-# LANGUAGE NoImplicitPrelude #-}

module Language.Haskell.TH.Subst
    ( substitute
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Map (Map)
import           Data.Maybe (fromMaybe)
import           Language.Haskell.TH

substitute :: Map Name Type -> Type -> Type
substitute s (ForallT b c t) = substitute s t & ForallT b c
substitute s (AppT f a) = AppT (substitute s f) (substitute s a)
substitute s (SigT t k) = SigT (substitute s t) k
substitute s (VarT n) = s ^. Lens.at n & fromMaybe (VarT n)
substitute s (InfixT l n r) = InfixT (substitute s l) n (substitute s r)
substitute s (UInfixT l n r) = UInfixT (substitute s l) n (substitute s r)
substitute s (ParensT t) = substitute s t & ParensT
substitute _ x = x
