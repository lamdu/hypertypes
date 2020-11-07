{-# LANGUAGE TemplateHaskellQuotes, CPP #-}

module Hyper.TH.Morph
    ( makeHMorph
    ) where

import qualified Control.Lens as Lens
import qualified Data.Map as Map
import           Hyper.Class.Morph
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Hyper.Internal.Prelude

makeHMorph :: Name -> DecsQ
makeHMorph typeName = makeTypeInfo typeName >>= makeHMorphForType

makeHMorphForType :: TypeInfo -> DecsQ
makeHMorphForType info =
    -- TODO: Contexts
    instanceD (pure []) (conT ''HMorph `appT` pure src `appT` pure dst)
    [ D.tySynInstDCompat
        ''MorphConstraint
        (Just [pure (PlainTV constraintVar)])
        ([src, dst, VarT constraintVar] <&> pure)
        (simplifyContext morphConstraint <&> toTuple)
    , DataInstD []
#if MIN_VERSION_template_haskell(2,15,0)
        Nothing (ConT ''MorphWitness `AppT` src `AppT` dst `AppT` WildCardT `AppT` WildCardT)
#else
        ''MorphWitness [src, dst, WildCardT, WildCardT]
#endif
        Nothing (witnesses ^.. traverse . Lens._2) []
        & pure
    , funD 'morphMap (tiConstructors info <&> pure . mkMorphCon)
    , funD 'morphLiftConstraint (liftConstraintClauses <&> pure)
    ]
    <&> (:[])
    where
        (s0, s1) = paramSubsts info
        src = D.applySubstitution s0 (tiInstance info)
        dst = D.applySubstitution s1 (tiInstance info)
        constraintVar = mkName "constraint"
        contents = childrenTypes info
        morphConstraint =
            (tcChildren contents ^.. Lens.folded <&> appSubsts (VarT constraintVar))
            <> (tcEmbeds contents ^.. Lens.folded <&>
                \x -> ConT ''MorphConstraint `appSubsts` x `AppT` VarT constraintVar)
        appSubsts x t = x `AppT` D.applySubstitution s0 t `AppT` D.applySubstitution s1 t
        nodeWits =
            tcChildren contents ^.. Lens.folded <&>
            \x ->
            let n = witPrefix <> mkNiceTypeName x & mkName in
            ( x
            , (n, GadtC [n] [] (appSubsts morphWithNessOf x))
            )
        embedWits =
            tcEmbeds contents ^.. Lens.folded <&>
            \x ->
            let n = witPrefix <> mkNiceTypeName x & mkName in
            ( x
            , ( n
                , GadtC [n] []
                    ( ArrowT `AppT` (ConT ''MorphWitness `appSubsts` x `AppT` varA `AppT` varB)
                        `AppT` (morphWithNessOf `AppT` varA `AppT` varB))
                )
            )
        witnesses = nodeWits <> embedWits & Map.fromList
        varA = VarT (mkName "a")
        varB = VarT (mkName "b")
        witPrefix = "M_" <> niceName (tiName info) <> "_"
        morphWithNessOf = ConT ''MorphWitness `AppT` src `AppT` dst
        liftConstraintClauses
            | Map.null witnesses = [Clause [] (NormalB (LamCaseE [])) []]
            | otherwise =
                (nodeWits ^.. traverse . Lens._2 . Lens._1 <&> liftNodeConstraint) <>
                (embedWits ^.. traverse . Lens._2 . Lens._1 <&> liftEmbedConstraint)
        liftNodeConstraint n = Clause [ConP n [], WildP] (NormalB (VarE 'id)) []
        liftEmbedConstraint n =
            Clause [ConP n [VarP varW], VarP varProxy]
            (NormalB (VarE 'morphLiftConstraint `AppE` VarE varW `AppE` VarE varProxy)) []
        varW = mkName "w"
        varProxy = mkName "p"
        mkMorphCon con =
            Clause [VarP varF, p] b []
            where
                (p, b) = morphCon 0 witnesses con

varF :: Name
varF = mkName "_f"

morphCon :: Int -> Map Type (Name, Con) -> (Name, a, [Either b CtrTypePattern]) -> (Pat, Body)
morphCon i witnesses (n, _, fields) =
    ( ConP n (cVars <&> VarP)
    , NormalB (foldl AppE (ConE n) (zipWith bodyFor fields cVars))
    )
    where
        cVars =
            [i ..] <&> show <&> ('x':) <&> mkName
            & take (length fields)
        bodyFor Left{} v = VarE v
        bodyFor (Right x) v = bodyForPat x `AppE` VarE v
        bodyForPat (Node x) = VarE varF `AppE` ConE (witnesses ^?! Lens.ix x . Lens._1)
        bodyForPat (InContainer _ pat) = VarE 'fmap `AppE` bodyForPat pat
        bodyForPat (FlatEmbed x) =
            LamCaseE
            (tiConstructors x
                <&> morphCon (i + length cVars) witnesses
                <&> \(p, b) -> Match p b []
            )
        bodyForPat (GenEmbed t) =
            VarE 'morphMap `AppE` (VarE varF `dot` ConE (witnesses ^?! Lens.ix t . Lens._1))

type MorphSubsts = (Map Name Type, Map Name Type)

paramSubsts :: TypeInfo -> MorphSubsts
paramSubsts info =
    (tiParams info <&> D.tvName) ^. traverse . Lens.to mkInfo
    where
        pinned = pinnedParams info
        mkInfo name
            | pinned ^. Lens.contains name = mempty
            | otherwise = (side name "0", side name "1")
        side name suffix = mempty & Lens.at name ?~ VarT (mkName (nameBase name <> suffix))

pinnedParams :: TypeInfo -> Set Name
pinnedParams = (^. Lens.to tiConstructors . traverse . Lens._3 . traverse . Lens.to ctrPinnedParams)

ctrPinnedParams :: Either Type CtrTypePattern -> Set Name
ctrPinnedParams (Left t) = typeParams t
ctrPinnedParams (Right Node{}) = mempty
ctrPinnedParams (Right GenEmbed{}) = mempty
ctrPinnedParams (Right (FlatEmbed info)) = pinnedParams info
ctrPinnedParams (Right (InContainer c p)) = typeParams c <> ctrPinnedParams (Right p)

typeParams :: Type -> Set Name
typeParams (VarT x) = mempty & Lens.contains x .~ True
typeParams (AppT f x) = typeParams f <> typeParams x
typeParams (InfixT x _ y) = typeParams x <> typeParams y
-- TODO: Missing cases
typeParams _ = mempty
