{-# LANGUAGE TemplateHaskell #-}

-- | Generate 'HFoldable' instances via @TemplateHaskell@
module Hyper.TH.Foldable
    ( makeHFoldable
    ) where

import qualified Control.Lens as Lens
import Hyper.Class.Foldable (HFoldable (..))
import Hyper.TH.Internal.Utils
import Language.Haskell.TH
import Language.Haskell.TH.Datatype (ConstructorVariant)

import Hyper.Internal.Prelude

-- | Generate a 'HFoldable' instance
makeHFoldable :: Name -> DecsQ
makeHFoldable typeName = makeTypeInfo typeName >>= makeHFoldableForType

makeHFoldableForType :: TypeInfo -> DecsQ
makeHFoldableForType info =
    instanceD
        (makeContext info >>= simplifyContext)
        [t|HFoldable $(pure (tiInstance info))|]
        [ InlineP 'hfoldMap Inline FunLike AllPhases & PragmaD & pure
        , funD 'hfoldMap (tiConstructors info <&> makeCtr)
        ]
        <&> (: [])
    where
        (_, wit) = makeNodeOf info
        makeCtr ctr =
            clause [varP varF, pat] body []
            where
                (pat, body) = makeHFoldMapCtr 0 wit ctr

makeContext :: TypeInfo -> Q [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._3 . traverse . Lens._Right
        & traverse ctxForPat
        <&> mconcat
    where
        ctxForPat (InContainer t pat) = (:) <$> [t|Foldable $(pure t)|] <*> ctxForPat pat
        ctxForPat (GenEmbed t) = [t|HFoldable $(pure t)|] <&> (: [])
        ctxForPat (FlatEmbed t) = makeContext t
        ctxForPat _ = pure []

varF :: Name
varF = mkName "_f"

makeHFoldMapCtr :: Int -> NodeWitnesses -> (Name, ConstructorVariant, [Either Type CtrTypePattern]) -> (Q Pat, Q Body)
makeHFoldMapCtr i wit (cName, _, cFields) =
    (conP cName (cVars <&> varP), body)
    where
        cVars =
            [i ..]
                <&> mkName . ("_x" <>) . show
                & take (length cFields)
        bodyParts =
            zipWith
                (\x y -> x <&> (`appE` y))
                (cFields <&> bodyFor)
                (cVars <&> varE)
                & concat
        body =
            case bodyParts of
                [] -> [|mempty|]
                _ -> foldl1 append bodyParts
                & normalB
        append x y = [|$x <> $y|]
        f = varE varF
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = []
        bodyForPat (Node t) = [[|$f $(nodeWit wit t)|]]
        bodyForPat (GenEmbed t) = [[|hfoldMap ($f . $(embedWit wit t))|]]
        bodyForPat (InContainer _ pat) = bodyForPat pat <&> appE [|foldMap|]
        bodyForPat (FlatEmbed x) =
            [ lamCaseE
                ( tiConstructors x
                    <&> uncurry match
                        . makeHFoldMapCtr (i + length cVars) wit
                        ?? []
                )
            ]
