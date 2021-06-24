{-# LANGUAGE TemplateHaskell, OverloadedStrings, FlexibleContexts, UndecidableInstances, FlexibleInstances #-}

module LangC where

import TypeLang (Name)

import Control.Lens.Operators
import Data.List.NonEmpty (NonEmpty(..), cons)
import Hyper
import Hyper.Class.Morph (morphMapped1)
import Hyper.Recurse ((##>>), wrap)
import Hyper.Syntax.App (App(..))
import Hyper.Syntax.Lam (Lam(..), lamOut)
import Hyper.Syntax.Let (Let(..))
import Hyper.Syntax.Row (RowExtend(..))
import Hyper.Syntax.Var (Var(..))

import Prelude

-- Demonstrating de-sugaring of a sugar-language to a core language:
-- * Let-expressions are replaced with redexes
-- * Cases and if-else expressions are replaced with applied lambda-cases

data CoreForms l h
    = CLit Int
    | CApp (App l h)
    | CVar (Var Name l h)
    | CLam (Lam Name l h)
    | CRecEmpty
    | CRecExtend (RowExtend Name l l h)
    | CGetField (h :# l) Name
    | CLamCaseEmpty
    | CLamCaseExtend (RowExtend Name l l h)
    | CInject (h :# l) Name
    deriving Generic

newtype LangCore h = LangCore (CoreForms LangCore h)

data IfThen h = IfThen (h :# LangSugar) (h :# LangSugar)
data Case h = Case Name Name (h :# LangSugar)

data LangSugar h
    = SBase (CoreForms LangSugar h)
    | SLet (Let Name LangSugar h)
    | SCase (h :# LangSugar) [Case h]
    | SIfElse (NonEmpty (IfThen h)) (h :# LangSugar)

makeHMorph ''CoreForms
makeHTraversableAndBases ''CoreForms
makeHTraversableAndBases ''LangCore
makeHTraversableAndBases ''IfThen
makeHTraversableAndBases ''Case
makeHTraversableAndBases ''LangSugar

instance RNodes LangSugar
instance RTraversable LangSugar
instance c LangSugar => Recursively c LangSugar

desugar :: Pure # LangSugar -> Pure # LangCore
desugar (Pure body) =
    case body of
    SBase x ->
        -- Note how we desugar all of the base forms without any boilerplate!
        x & morphMapped1 %~ desugar & core
    SLet x ->
        cLam v i `cApp` e
        where
            Let v i e = x & morphMapped1 %~ desugar
    SCase e h ->
        foldr step cAbsurd h `cApp` desugar e
        where
            step (Case c v b) = cAddLamCase c (v `cLam` desugar b)
    SIfElse g e ->
        foldr step (desugar e) g
        where
            step (IfThen c t) r =
                cAddLamCase "True" (cLam "_" (desugar t))
                (cAddLamCase "False" (cLam "_" r) cAbsurd)
                `cApp` desugar c
    where
        core = Pure . LangCore
        cApp x = core . CApp . App x
        cLam v = core . CLam . Lam v
        cAbsurd = core CLamCaseEmpty
        cAddLamCase c h = core . CLamCaseExtend . RowExtend c h

-- Lift core language into the surface language
coreToSugar :: Pure # LangCore -> Pure # LangSugar
coreToSugar (Pure (LangCore x)) = x & morphMapped1 %~ coreToSugar & SBase & Pure

-- Convert top-level expression to sugared form when possible
sugarizeTop :: LangSugar # Pure -> LangSugar # Pure
sugarizeTop top@(SBase (CApp (App (Pure (SBase func)) arg))) =
    case func of
    CLam (Lam v b) -> Let v arg b & SLet
    CLamCaseExtend (RowExtend c0 (Pure (SBase (CLam h0))) r0) ->
        go ((c0, h0) :| []) r0
        where
            go cases (Pure (SBase CLamCaseEmpty)) =
                case cases of
                ("True", t) :| [("False", f)] | checkIf t f -> makeIf t f
                ("False", f) :| [("True", t)] | checkIf t f -> makeIf t f
                _ ->
                    cases ^.. traverse
                    <&> (\(n, Lam v b) -> Case n v b)
                    & SCase arg
                where
                    makeIf t f =
                        case f ^. lamOut of
                        Pure (SIfElse is e) -> SIfElse (cons i is) e
                        _ -> SIfElse (pure i) (f ^. lamOut)
                        where
                            i = IfThen arg (t ^. lamOut)
            go cases (Pure (SBase (CLamCaseExtend (RowExtend c (Pure (SBase (CLam h))) r)))) =
                go (cons (c, h) cases) r
            go _ _ = top
            checkIf t f = checkIfBranch t && checkIfBranch f
            checkIfBranch (Lam v b) = not (usesVar v b)
    _ -> top
sugarizeTop x = x

usesVar :: Name -> Pure # LangSugar -> Bool
usesVar v (Pure (SBase (CVar (Var x)))) = v == x
usesVar v (Pure x) = any (usesVar v) (x ^.. hfolded1)

sugarize :: Pure # LangSugar -> Pure # LangSugar
sugarize = wrap (Proxy @((~) LangSugar) ##>> Pure . sugarizeTop)
