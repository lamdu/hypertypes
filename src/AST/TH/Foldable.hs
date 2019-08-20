{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Foldable
    ( makeKFoldable
    ) where

import           AST.Class.Foldable
import           AST.TH.Internal
import           Control.Lens.Operators
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKFoldable :: Name -> DecsQ
makeKFoldable typeName = makeTypeInfo typeName >>= makeKFoldableForType

makeKFoldableForType :: TypeInfo -> DecsQ
makeKFoldableForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KFoldable) (pure (tiInstance info)))
    [ InlineP 'foldMapK Inline FunLike AllPhases & PragmaD & pure
    , funD 'foldMapK (tiCons info <&> pure . makeFoldMapKCtr [] (VarE 'foldMapK) (tiVar info))
    , InlineP 'foldMapKWith Inline FunLike AllPhases & PragmaD & pure
    , funD 'foldMapKWith (tiCons info <&> pure . makeFoldMapKCtr [VarP proxy] (VarE 'foldMapKWith `AppE` VarE proxy) (tiVar info))
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
        ctxForPat (Tof t pat) = (ConT ''Foldable `AppT` t) : ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KFoldable `AppT` t]
        ctxForPat _ = []

varF :: Name
varF = mkName "_f"

makeFoldMapKCtr :: [Pat] -> Exp -> Name -> D.ConstructorInfo -> Clause
makeFoldMapKCtr patBase inner knot info =
    Clause (patBase <> [VarP varF, ConP (D.constructorName info) (cVars <&> VarP)]) body []
    where
        cVars =
            [0::Int ..] <&> show <&> ("_x" <>) <&> mkName
            & take (length (D.constructorFields info))
        bodyParts =
            zipWith (\x y -> x <&> (`AppE` y))
            (pats <&> bodyForPat)
            (cVars <&> VarE)
            & concat
        body =
            case bodyParts of
            [] -> VarE 'mempty
            _ -> foldl1 append bodyParts
            & NormalB
        append x y = InfixE (Just x) (VarE '(<>)) (Just y)
        pats = D.constructorFields info <&> matchType knot
        bodyForPat NodeFofX{} = [VarE varF]
        bodyForPat XofF{} = [inner `AppE` VarE varF]
        bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'foldMap)
        bodyForPat Other{} = []
