{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Functor
    ( makeKFunctor, makeKFunctorRules
    ) where

import           AST.Class.Functor
import           AST.Knot (Tree)
import           AST.TH.Internal
import           Control.Lens.Operators
import           Data.Proxy (Proxy)
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKFunctor :: Name -> DecsQ
makeKFunctor typeName = makeTypeInfo typeName >>= makeKFunctorForType

makeKFunctorForType :: TypeInfo -> DecsQ
makeKFunctorForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KFunctor) (pure (tiInstance info)))
    [ InlineP 'mapK Inline FunLike AllPhases & PragmaD & pure
    , funD 'mapK (tiCons info <&> pure . makeMapKCtr [] (VarE 'mapK) (tiVar info))
    , InlineP 'mapKWith Inline FunLike AllPhases & PragmaD & pure
    , funD 'mapKWith (tiCons info <&> pure . makeMapKCtr [VarP proxy] (VarE 'mapKWith `AppE` VarE proxy) (tiVar info))
    ] <&> (:[])
    where
        proxy = mkName "_p"

makeKFunctorRules :: Name -> DecsQ
makeKFunctorRules typeName =
    makeTypeInfo typeName
    <&>
    \info ->
    [ RuleP
        ("mapKWith/" <> show typeName)
        [ TypedRuleVar constraintProxyVar
            (ConT ''Proxy `AppT` VarT constraintVar
            )
        , TypedRuleVar funcVar
            (ForallT [PlainTV childVar]
                [VarT constraintVar `AppT` VarT childVar]
                (ArrowT
                    `AppT` (ConT ''Tree `AppT` VarT varM `AppT` VarT childVar)
                    `AppT` (ConT ''Tree `AppT` VarT varN `AppT` VarT childVar))
            )
        ]
        (VarE 'mapKWith `AppTypeE` tiInstance info
            `AppE` VarE constraintProxyVar `AppE` VarE funcVar)
        (LamCaseE
            ( tiCons info
                <&> makeMapKRule funcVar
                    (VarE 'mapKWith `AppE` VarE constraintProxyVar)
                    (tiVar info)
            )
        )
        AllPhases
        & PragmaD
        -- I don't know how to quantify over type variables in rewrite rules,
        -- so avoid rules in these cases for now.
        | null (D.freeVariables (tiInstance info))
    ]
    where
        constraintProxyVar = mkName "_constraintProxy"
        constraintVar = mkName "_constraint"
        funcVar = mkName "_func"
        childVar = mkName "_child"
        varM = mkName "_m"
        varN = mkName "_n"

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (Tof t pat) = (ConT ''Functor `AppT` t) : ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KFunctor `AppT` t]
        ctxForPat _ = []

makeMapKCtr :: [Pat] -> Exp -> Name -> D.ConstructorInfo -> Clause
makeMapKCtr patBase inner knot info =
    Clause (patBase <> [VarP varF, pat]) body []
    where
        (pat, body) = mapKCtrCase varF inner knot info
        varF = mkName "_f"

makeMapKRule :: Name -> Exp -> Name -> D.ConstructorInfo -> Match
makeMapKRule funcVar inner knot info =
    Match pat body []
    where
        (pat, body) = mapKCtrCase funcVar inner knot info

mapKCtrCase :: Name -> Exp -> Name -> D.ConstructorInfo -> (Pat, Body)
mapKCtrCase varF inner knot info =
    ( ConP (D.constructorName info) (cVars <&> VarP)
    , zipWith AppE
        (pats <&> bodyForPat)
        (cVars <&> VarE)
        & foldl AppE (ConE (D.constructorName info))
        & NormalB
    )
    where
        cVars =
            [0::Int ..] <&> show <&> ('x':) <&> mkName
            & take (length (D.constructorFields info))
        pats = D.constructorFields info <&> matchType knot
        bodyForPat NodeFofX{} = VarE varF
        bodyForPat XofF{} = inner `AppE` VarE varF
        bodyForPat (Tof _ pat) = bodyForPat pat & AppE (VarE 'fmap)
        bodyForPat Other{} = VarE 'id
