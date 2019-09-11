{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KFoldable' instances via @TemplateHaskell@

module AST.TH.Foldable
    ( makeKFoldable
    ) where

import           AST.Class.Foldable
import           AST.TH.Internal.Utils
import           Control.Lens.Operators
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

-- | Generate a 'KFoldable' instance
makeKFoldable :: Name -> DecsQ
makeKFoldable typeName = makeTypeInfo typeName >>= makeKFoldableForType

makeKFoldableForType :: TypeInfo -> DecsQ
makeKFoldableForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KFoldable) (pure (tiInstance info)))
    [ InlineP 'foldMapK Inline FunLike AllPhases & PragmaD & pure
    , funD 'foldMapK (tiCons info <&> pure . makeFoldMapKCtr wit (tiVar info))
    ]
    <&> (:[])
    where
        (_, wit) = makeNodeOf info

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

makeFoldMapKCtr :: NodeWitnesses -> Name -> D.ConstructorInfo -> Clause
makeFoldMapKCtr wit knot info =
    Clause [VarP varF, ConP (D.constructorName info) (cVars <&> VarP)] body []
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
        bodyForPat (NodeFofX t) = [VarE varF `AppE` nodeWit wit t]
        bodyForPat (XofF t) = [VarE 'foldMapK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))]
        bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'foldMap)
        bodyForPat Other{} = []
