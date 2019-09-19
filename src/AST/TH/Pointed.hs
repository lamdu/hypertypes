{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KPointed' instances via @TemplateHaskell@

module AST.TH.Pointed
    ( makeKPointed
    ) where

import           AST.Class.Pointed
import           AST.TH.Internal.Utils
import           Control.Lens.Operators
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

-- | Generate a 'KPointed' instance
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
            , funD 'pureK [makePureKCtr info cons & pure]
            ]
    <&> (:[])

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (InContainer t pat) = (ConT ''Applicative `AppT` t) : ctxForPat pat
        ctxForPat (Embed t) = [ConT ''KPointed `AppT` t]
        ctxForPat (PlainData t) = [ConT ''Monoid `AppT` t]
        ctxForPat _ = []

makePureKCtr :: TypeInfo -> D.ConstructorInfo -> Clause
makePureKCtr typeInfo ctrInfo =
    Clause [VarP varF] body []
    where
        body =
            D.constructorFields ctrInfo
            <&> matchType (tiVar typeInfo)
            <&> bodyForPat
            & foldl AppE (ConE (D.constructorName ctrInfo))
            & NormalB
        bodyForPat (Node t) = VarE varF `AppE` nodeWit wit t
        bodyForPat (Embed t) = VarE 'pureK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))
        bodyForPat (InContainer _ pat) = bodyForPat pat & AppE (VarE 'pure)
        bodyForPat PlainData{} = VarE 'mempty
        varF = mkName "_f"
        (_, wit) = makeNodeOf typeInfo
