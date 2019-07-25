{-# LANGUAGE NoImplicitPrelude, TemplateHaskellQuotes #-}

module AST.Class.Pointed.TH
    ( makeKPointed
    ) where

import           AST.Class
import           AST.Internal.TH
import           Control.Lens.Operators
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKPointed :: Name -> DecsQ
makeKPointed typeName = makeTypeInfo typeName >>= makeKPointedForType

makeKPointedForType :: TypeInfo -> DecsQ
makeKPointedForType info =
    do
        cons <-
            case tiCons info of
            [x] -> pure x
            _ -> fail "makeKPointed only supports types with a single constructor"
        childrenInfo <- makeNodeTypesInfo info
        let pureCDecl
                | childrenTypesType childrenInfo == tiInstance info =
                    Clause [] (NormalB (VarE 'id)) [] & pure
                | otherwise = makePureCCtr childrenInfo (tiVar info) cons
        instanceD (simplifyContext (makeContext info)) (appT (conT ''KPointed) (pure (tiInstance info)))
            [ tySynInstD ''KLiftConstraint
                (pure (TySynEqn [tiInstance info, VarT constraintVar] liftedConstraint))
            , InlineP 'pureC Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureC [pureCDecl]
            , InlineP 'pureK Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureK [makePureKCtr (tiVar info) cons]
            , InlineP 'pureKWithConstraint Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureKWithConstraint [makePureKWithCtr (tiVar info) cons]
            ]
    <&> (:[])
    where
        contents = tiContents info
        liftedConstraint =
            (Set.toList (tcChildren contents) <&> (VarT constraintVar `AppT`))
            <> (Set.toList (tcEmbeds contents) <&>
                \x -> ConT ''KLiftConstraint `AppT` x `AppT` VarT constraintVar)
            <> Set.toList (tcOthers contents)
            & toTuple

constraintVar :: Name
constraintVar = mkName "constraint"

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (Tof t pat) = (ConT ''Applicative `AppT` t) : ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KPointed `AppT` t]
        ctxForPat _ = []

varF :: Name
varF = mkName "_f"

makePureKCtr :: Name -> D.ConstructorInfo -> Q Clause
makePureKCtr knot info =
    D.constructorFields info
    <&> matchType knot
    & traverse bodyForPat
    <&> foldl AppE (ConE (D.constructorName info))
    <&> NormalB
    <&> \x -> Clause [VarP varF] x []
    where
        bodyForPat NodeFofX{} = VarE varF & pure
        bodyForPat XofF{} = VarE 'pureK `AppE` VarE varF & pure
        bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'pure)
        bodyForPat (Other x) = fail ("KPointed can't produce value of type " <> show x)

makePureKWithCtr :: Name -> D.ConstructorInfo -> Q Clause
makePureKWithCtr knot info =
    D.constructorFields info
    <&> matchType knot
    & traverse bodyForPat
    <&> foldl AppE (ConE (D.constructorName info))
    <&> NormalB
    <&> \x -> Clause [VarP proxy, VarP varF] x []
    where
        proxy = mkName "_p"
        bodyForPat NodeFofX{} = VarE varF & pure
        bodyForPat XofF{} = VarE 'pureKWithConstraint `AppE` VarE proxy `AppE` VarE varF & pure
        bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'pure)
        bodyForPat (Other x) = fail ("KPointed can't produce value of type " <> show x)

makePureCCtr :: NodeTypesInfo -> Name -> D.ConstructorInfo -> Q Clause
makePureCCtr childrenInfo knot info =
    do
        let bodyForPat (NodeFofX t) =
                case Map.lookup t (varsForChildTypes childrenInfo) of
                Nothing ->
                    "Failed producing pureC for child of type:\n        " <> show t <>
                    "\n    not in:\n        " <> show (varsForChildTypes childrenInfo)
                    & fail
                Just x -> VarE x & pure
            bodyForPat (XofF t) =
                getEmbedTypes childrenInfo t <&> AppE (VarE 'pureC)
            bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'pure)
            bodyForPat (Other x) = fail ("KPointed can't produce value of type " <> show x)
        D.constructorFields info
            <&> matchType knot
            & traverse bodyForPat
            <&> foldl AppE (ConE (D.constructorName info))
            <&> NormalB
            <&> \x -> Clause [childrenTypesPat childrenInfo] x []
