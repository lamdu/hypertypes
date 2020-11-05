{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}

module LangC where

import TypeLang (Name)

import Control.Lens.Operators
import Data.List.NonEmpty (NonEmpty)
import Hyper
import Hyper.Class.Morph
import Hyper.Type.AST.App (App(..))
import Hyper.Type.AST.Lam (Lam(..))
import Hyper.Type.AST.Let (Let(..))
import Hyper.Type.AST.Row (RowExtend(..))
import Hyper.Type.AST.Var (Var)

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

makeHMorph ''CoreForms

newtype LangCore h = LangCore (CoreForms LangCore h)

data LangSugar h
    = SBase (CoreForms LangSugar h)
    | SLet (Let Name LangSugar h)
    | SCase (h :# LangSugar) [(Name, Name, h :# LangSugar)]
    | SIfElse (NonEmpty (h :# LangSugar, h :# LangSugar)) (h :# LangSugar)

type SugarToCore = HIs2 LangSugar LangCore

desugar :: Pure # LangSugar -> Pure # LangCore
desugar (Pure body) =
    case body of
    SBase x ->
        -- Note how we desugar all of the base forms without any boilerplate!
        morphMap (Proxy @SugarToCore #?> desugar) x & core
    SLet x ->
        cLam v i `cApp` e
        where
            Let v i e = morphMap (Proxy @SugarToCore #?> desugar) x
    SCase e h ->
        foldr step cAbsurd h `cApp` desugar e
        where
            step (c, v, b) = cAddLamCase c (v `cLam` desugar b)
    SIfElse g e ->
        foldr step (desugar e) g
        where
            step (c, t) r =
                cAddLamCase "True" (cLam "_" (desugar t))
                (cAddLamCase "False" (cLam "_" r) cAbsurd)
                `cApp` desugar c
    where
        core = Pure . LangCore
        cApp x = core . CApp . App x
        cLam v = core . CLam . Lam v
        cAbsurd = core CLamCaseEmpty
        cAddLamCase c h = core . CLamCaseExtend . RowExtend c h

coreToSugar :: Pure # LangCore -> Pure # LangSugar
coreToSugar (Pure (LangCore body)) = morphMap (Proxy @(HIs2 LangCore LangSugar) #?> coreToSugar) body & SBase & Pure
