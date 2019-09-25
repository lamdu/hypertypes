{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KFoldable' instances via @TemplateHaskell@

module Hyper.TH.Foldable
    ( makeKFoldable
    ) where

import           Hyper.Class.Foldable
import           Hyper.TH.Internal.Utils
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'KFoldable' instance
makeKFoldable :: Name -> DecsQ
makeKFoldable typeName = makeTypeInfo typeName >>= makeKFoldableForType

makeKFoldableForType :: TypeInfo -> DecsQ
makeKFoldableForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KFoldable) (pure (tiInstance info)))
    [ InlineP 'foldMapK Inline FunLike AllPhases & PragmaD & pure
    , funD 'foldMapK (tiConstructors info <&> pure . makeCtr)
    ]
    <&> (:[])
    where
        (_, wit) = makeNodeOf info
        makeCtr ctr =
            Clause [VarP varF, pat] body []
            where
                (pat, body) = makeFoldMapKCtr 0 wit ctr

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._2 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer t pat) = (ConT ''Foldable `AppT` t) : ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''KFoldable `AppT` t]
        ctxForPat _ = []

varF :: Name
varF = mkName "_f"

makeFoldMapKCtr :: Int -> NodeWitnesses -> (Name, [Either Type CtrTypePattern]) -> (Pat, Body)
makeFoldMapKCtr i wit (cName, cFields) =
    (ConP cName (cVars <&> VarP), body)
    where
        cVars =
            [i ..] <&> show <&> ("_x" <>) <&> mkName
            & take (length cFields)
        bodyParts =
            zipWith (\x y -> x <&> (`AppE` y))
            (cFields <&> bodyFor)
            (cVars <&> VarE)
            & concat
        body =
            case bodyParts of
            [] -> VarE 'mempty
            _ -> foldl1 append bodyParts
            & NormalB
        append x y = InfixE (Just x) (VarE '(<>)) (Just y)
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = []
        bodyForPat (Node t) = [VarE varF `AppE` nodeWit wit t]
        bodyForPat (GenEmbed t) = [VarE 'foldMapK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))]
        bodyForPat (InContainer _ pat) = bodyForPat pat <&> AppE (VarE 'foldMap)
        bodyForPat (FlatEmbed x) =
            [ LamCaseE
                (tiConstructors x
                    <&> makeFoldMapKCtr (i + length cVars) wit
                    <&> \(p, b) -> Match p b []
                )
            ]
