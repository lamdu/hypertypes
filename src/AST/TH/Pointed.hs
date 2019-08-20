{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Pointed
    ( makeKPointed
    ) where

import           AST.Class
import           AST.TH.Internal
import           Control.Lens.Operators
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
        instanceD (simplifyContext (makeContext info)) (appT (conT ''KPointed) (pure (tiInstance info)))
            [ InlineP 'pureK Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureK [makePureKCtr [] (VarE 'pureK) (tiVar info) cons & pure]
            , InlineP 'pureKWith Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureKWith [makePureKCtr [VarP proxy] (VarE 'pureKWith `AppE` VarE proxy) (tiVar info) cons & pure]
            ]
    <&> (:[])
    where
        proxy = mkName "_p"

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (Tof t pat) = (ConT ''Applicative `AppT` t) : ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KPointed `AppT` t]
        ctxForPat (Other t) = [ConT ''Monoid `AppT` t]
        ctxForPat _ = []

makePureKCtr :: [Pat] -> Exp -> Name -> D.ConstructorInfo -> Clause
makePureKCtr patBase inner knot info =
    Clause (patBase <> [VarP varF]) body []
    where
        body =
            D.constructorFields info
            <&> matchType knot
            <&> bodyForPat
            & foldl AppE (ConE (D.constructorName info))
            & NormalB
        bodyForPat NodeFofX{} = VarE varF
        bodyForPat XofF{} = inner `AppE` VarE varF
        bodyForPat (Tof _ pat) = bodyForPat pat & AppE (VarE 'pure)
        bodyForPat Other{} = VarE 'mempty
        varF = mkName "_f"
