{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KFoldable' instances via @TemplateHaskell@

module AST.TH.Foldable
    ( makeKFoldable
    ) where

import           AST.Class.Foldable
import           AST.TH.Internal.Utils
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
    , funD 'foldMapK (tiConstructors info <&> pure . uncurry (makeFoldMapKCtr wit))
    ]
    <&> (:[])
    where
        (_, wit) = makeNodeOf info

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._2 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer t pat) = (ConT ''Foldable `AppT` t) : ctxForPat pat
        ctxForPat (Embed t) = [ConT ''KFoldable `AppT` t]
        ctxForPat _ = []

varF :: Name
varF = mkName "_f"

makeFoldMapKCtr :: NodeWitnesses -> Name -> [Either Type CtrTypePattern] -> Clause
makeFoldMapKCtr wit cName cFields =
    Clause [VarP varF, ConP cName (cVars <&> VarP)] body []
    where
        cVars =
            [0::Int ..] <&> show <&> ("_x" <>) <&> mkName
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
        bodyForPat (Embed t) = [VarE 'foldMapK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))]
        bodyForPat (InContainer _ pat) = bodyForPat pat <&> AppE (VarE 'foldMap)
