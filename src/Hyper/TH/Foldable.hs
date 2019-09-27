{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'HFoldable' instances via @TemplateHaskell@

module Hyper.TH.Foldable
    ( makeHFoldable
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Hyper.Class.Foldable
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'HFoldable' instance
makeHFoldable :: Name -> DecsQ
makeHFoldable typeName = makeTypeInfo typeName >>= makeHFoldableForType

makeHFoldableForType :: TypeInfo -> DecsQ
makeHFoldableForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''HFoldable) (pure (tiInstance info)))
    [ InlineP 'hfoldMap Inline FunLike AllPhases & PragmaD & pure
    , funD 'hfoldMap (tiConstructors info <&> pure . makeCtr)
    ]
    <&> (:[])
    where
        (_, wit) = makeNodeOf info
        makeCtr ctr =
            Clause [VarP varF, pat] body []
            where
                (pat, body) = makeFoldMapHCtr 0 wit ctr

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._2 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer t pat) = (ConT ''Foldable `AppT` t) : ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''HFoldable `AppT` t]
        ctxForPat _ = []

varF :: Name
varF = mkName "_f"

makeFoldMapHCtr :: Int -> NodeWitnesses -> (Name, [Either Type CtrTypePattern]) -> (Pat, Body)
makeFoldMapHCtr i wit (cName, cFields) =
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
        bodyForPat (GenEmbed t) = [VarE 'hfoldMap `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))]
        bodyForPat (InContainer _ pat) = bodyForPat pat <&> AppE (VarE 'foldMap)
        bodyForPat (FlatEmbed x) =
            [ LamCaseE
                (tiConstructors x
                    <&> makeFoldMapHCtr (i + length cVars) wit
                    <&> \(p, b) -> Match p b []
                )
            ]
