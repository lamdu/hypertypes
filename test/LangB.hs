{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module LangB where

import TypeLang

import Control.Applicative
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.Except
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.ST.Class (MonadST (..))
import Data.Map (Map)
import Data.STRef
import Data.String (IsString (..))
import Generics.Constraints (makeDerivings)
import Hyper
import Hyper.Class.Recursive
import Hyper.Infer
import Hyper.Infer.Blame
import Hyper.Syntax
import Hyper.Syntax.Nominal
import Hyper.Syntax.Row
import Hyper.Syntax.Scheme
import Hyper.Unify
import Hyper.Unify.Binding
import Hyper.Unify.Binding.ST
import Hyper.Unify.Generalize
import Hyper.Unify.New
import Hyper.Unify.QuantifiedVar
import Hyper.Unify.Term
import qualified Text.PrettyPrint as P
import Text.PrettyPrint.HughesPJClass (Pretty (..), maybeParens)

import Prelude

data LangB h
    = BLit Int
    | BApp (App LangB h)
    | BVar (Var Name LangB h)
    | BLam (Lam Name LangB h)
    | BLet (Let Name LangB h)
    | BRecEmpty
    | BRecExtend (RowExtend Name LangB LangB h)
    | BGetField (h :# LangB) Name
    | BToNom (ToNom Name LangB h)
    deriving (Generic)

makeHTraversableAndBases ''LangB
makeHMorph ''LangB
instance c LangB => Recursively c LangB
instance RNodes LangB
instance RTraversable LangB

instance Recursive ((~) LangB) where recurse _ = Dict

type instance InferOf LangB = ANode Typ
type instance ScopeOf LangB = ScopeTypes

instance HasInferredType LangB where
    type TypeOf LangB = Typ
    inferredType _ = _ANode

instance Pretty (LangB # Pure) where
    pPrintPrec _ _ (BLit i) = pPrint i
    pPrintPrec _ _ BRecEmpty = P.text "{}"
    pPrintPrec lvl p (BRecExtend (RowExtend h v r)) =
        pPrintPrec lvl 20 h
            P.<+> P.text "="
            P.<+> (pPrintPrec lvl 2 v <> P.text ",")
            P.<+> pPrintPrec lvl 1 r
            & maybeParens (p > 1)
    pPrintPrec lvl p (BApp x) = pPrintPrec lvl p x
    pPrintPrec lvl p (BVar x) = pPrintPrec lvl p x
    pPrintPrec lvl p (BLam x) = pPrintPrec lvl p x
    pPrintPrec lvl p (BLet x) = pPrintPrec lvl p x
    pPrintPrec lvl p (BGetField w h) = pPrintPrec lvl p w <> P.text "." <> pPrint h
    pPrintPrec lvl p (BToNom n) = pPrintPrec lvl p n

instance VarType Name LangB where
    varType _ h (ScopeTypes t) =
        r t
        where
            r ::
                forall m.
                UnifyGen m Typ =>
                Map Name (HFlip GTerm Typ # UVarOf m) ->
                m (UVarOf m # Typ)
            r x = x ^?! Lens.ix h . _HFlip & instantiate

instance
    ( MonadScopeLevel m
    , LocalScopeType Name (UVarOf m # Typ) m
    , LocalScopeType Name (GTerm (UVarOf m) # Typ) m
    , UnifyGen m Typ
    , UnifyGen m Row
    , HasScope m ScopeTypes
    , MonadNominals Name Typ m
    ) =>
    Infer m LangB
    where
    inferBody (BApp x) = inferBody x <&> Lens._1 %~ BApp
    inferBody (BVar x) = inferBody x <&> Lens._1 %~ BVar
    inferBody (BLam x) = inferBody x <&> Lens._1 %~ BLam
    inferBody (BLet x) = inferBody x <&> Lens._1 %~ BLet
    inferBody (BLit x) = newTerm TInt <&> (BLit x,) . MkANode
    inferBody (BToNom x) =
        do
            (b, t) <- inferBody x
            TNom t & newTerm <&> (BToNom b,) . MkANode
    inferBody (BRecExtend (RowExtend h v r)) =
        do
            InferredChild vI vT <- inferChild v
            InferredChild rI rT <- inferChild r
            restR <-
                scopeConstraints (Proxy @Row)
                    <&> rForbiddenFields . Lens.contains h .~ True
                    >>= newVar binding . UUnbound
            _ <- TRec restR & newTerm >>= unify (rT ^. _ANode)
            RowExtend h (vT ^. _ANode) restR
                & RExtend
                & newTerm
                >>= newTerm . TRec
                <&> (BRecExtend (RowExtend h vI rI),) . MkANode
    inferBody BRecEmpty =
        newTerm REmpty >>= newTerm . TRec <&> (BRecEmpty,) . MkANode
    inferBody (BGetField w h) =
        do
            (rT, wR) <- rowElementInfer RExtend h
            InferredChild wI wT <- inferChild w
            (BGetField wI h, _ANode # rT)
                <$ (newTerm (TRec wR) >>= unify (wT ^. _ANode))

-- Monads for inferring `LangB`:

newtype ScopeTypes v = ScopeTypes (Map Name (HFlip GTerm Typ v))
    deriving stock (Generic)
    deriving newtype (Semigroup, Monoid)

makeDerivings [''Show] [''LangB, ''ScopeTypes]
makeHTraversableAndBases ''ScopeTypes

makeHasHPlain [''LangB]
instance IsString (HPlain LangB) where
    fromString = BVarP . fromString

Lens.makePrisms ''ScopeTypes

data InferScope v = InferScope
    { _varSchemes :: ScopeTypes # v
    , _scopeLevel :: ScopeLevel
    , _nominals :: Map Name (LoadedNominalDecl Typ # v)
    }
Lens.makeLenses ''InferScope

emptyInferScope :: InferScope v
emptyInferScope = InferScope mempty (ScopeLevel 0) mempty

newtype PureInferB a
    = PureInferB
        ( RWST
            (InferScope UVar)
            ()
            PureInferState
            (Either (TypeError # Pure))
            a
        )
    deriving newtype
        ( Functor
        , Applicative
        , Monad
        , MonadError (TypeError # Pure)
        , MonadReader (InferScope UVar)
        , MonadState PureInferState
        )

Lens.makePrisms ''PureInferB

execPureInferB :: PureInferB a -> Either (TypeError # Pure) a
execPureInferB act =
    runRWST (act ^. _PureInferB) emptyInferScope emptyPureInferState
        <&> (^. Lens._1)

type instance UVarOf PureInferB = UVar

instance MonadNominals Name Typ PureInferB where
    getNominalDecl name = Lens.view nominals <&> (^?! Lens.ix name)

instance HasScope PureInferB ScopeTypes where
    getScope = Lens.view varSchemes

instance LocalScopeType Name (UVar # Typ) PureInferB where
    localScopeType h v = local (varSchemes . _ScopeTypes . Lens.at h ?~ MkHFlip (GMono v))

instance LocalScopeType Name (GTerm UVar # Typ) PureInferB where
    localScopeType h v = local (varSchemes . _ScopeTypes . Lens.at h ?~ MkHFlip v)

instance MonadScopeLevel PureInferB where
    localLevel = local (scopeLevel . _ScopeLevel +~ 1)

instance UnifyGen PureInferB Typ where
    scopeConstraints _ = Lens.view scopeLevel

instance UnifyGen PureInferB Row where
    scopeConstraints _ = Lens.view scopeLevel <&> RowConstraints mempty

instance MonadQuantify ScopeLevel Name PureInferB where
    newQuantifiedVariable _ =
        pisFreshQVars . tTyp . Lens._Wrapped <<+= 1 <&> Name . ('t' :) . show

instance MonadQuantify RConstraints Name PureInferB where
    newQuantifiedVariable _ =
        pisFreshQVars . tRow . Lens._Wrapped <<+= 1 <&> Name . ('r' :) . show

instance Unify PureInferB Typ where
    binding = bindingDict (pisBindings . tTyp)

instance Unify PureInferB Row where
    binding = bindingDict (pisBindings . tRow)
    structureMismatch = rStructureMismatch

instance HasScheme Types PureInferB Typ
instance HasScheme Types PureInferB Row

newtype STInferB s a
    = STInferB
        ( ReaderT
            (InferScope (STUVar s), STNameGen s)
            (ExceptT (TypeError # Pure) (ST s))
            a
        )
    deriving newtype
        ( Functor
        , Applicative
        , Monad
        , MonadST
        , MonadError (TypeError # Pure)
        , MonadReader (InferScope (STUVar s), STNameGen s)
        )

Lens.makePrisms ''STInferB

execSTInferB :: STInferB s a -> ST s (Either (TypeError # Pure) a)
execSTInferB act =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT (act ^. _STInferB) (emptyInferScope, qvarGen) & runExceptT

type instance UVarOf (STInferB s) = STUVar s

instance MonadNominals Name Typ (STInferB s) where
    getNominalDecl name = Lens.view (Lens._1 . nominals) <&> (^?! Lens.ix name)

instance HasScope (STInferB s) ScopeTypes where
    getScope = Lens.view (Lens._1 . varSchemes)

instance LocalScopeType Name (STUVar s # Typ) (STInferB s) where
    localScopeType h v = local (Lens._1 . varSchemes . _ScopeTypes . Lens.at h ?~ MkHFlip (GMono v))

instance LocalScopeType Name (GTerm (STUVar s) # Typ) (STInferB s) where
    localScopeType h v = local (Lens._1 . varSchemes . _ScopeTypes . Lens.at h ?~ MkHFlip v)

instance MonadScopeLevel (STInferB s) where
    localLevel = local (Lens._1 . scopeLevel . _ScopeLevel +~ 1)

instance UnifyGen (STInferB s) Typ where
    scopeConstraints _ = Lens.view (Lens._1 . scopeLevel)

instance UnifyGen (STInferB s) Row where
    scopeConstraints _ = Lens.view (Lens._1 . scopeLevel) <&> RowConstraints mempty

instance MonadQuantify ScopeLevel Name (STInferB s) where
    newQuantifiedVariable _ = newStQuantified (Lens._2 . tTyp) <&> Name . ('t' :) . show

instance MonadQuantify RConstraints Name (STInferB s) where
    newQuantifiedVariable _ = newStQuantified (Lens._2 . tRow) <&> Name . ('r' :) . show

instance Unify (STInferB s) Typ where
    binding = stBinding

instance Unify (STInferB s) Row where
    binding = stBinding
    structureMismatch = rStructureMismatch

instance HasScheme Types (STInferB s) Typ
instance HasScheme Types (STInferB s) Row

instance Blame PureInferB LangB where
    inferOfUnify _ x y = unify (x ^. _ANode) (y ^. _ANode) & void
    inferOfMatches _ x y =
        (==)
            <$> (semiPruneLookup (x ^. _ANode) <&> fst)
            <*> (semiPruneLookup (y ^. _ANode) <&> fst)
