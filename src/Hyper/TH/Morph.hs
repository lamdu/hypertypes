{-# LANGUAGE TemplateHaskell, CPP #-}

module Hyper.TH.Morph
    ( makeHMorph
    ) where

import qualified Control.Lens as Lens
import qualified Data.Map as Map
import           Hyper.Class.Morph (HMorph(..))
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Hyper.Internal.Prelude

makeHMorph :: Name -> DecsQ
makeHMorph typeName = makeTypeInfo typeName >>= makeHMorphForType

makeHMorphForType :: TypeInfo -> DecsQ
makeHMorphForType info =
    -- TODO: Contexts
    instanceD (pure []) [t|HMorph $(pure src) $(pure dst)|]
    [ D.tySynInstDCompat
        ''MorphConstraint
        (Just [pure (plainTV constraintVar)])
        ([src, dst, VarT constraintVar] <&> pure)
        (simplifyContext morphConstraint <&> toTuple)
    , dataInstD
        (pure []) ''MorphWitness [pure src, pure dst, [t|_|], [t|_|]]
        Nothing (witnesses ^.. traverse . Lens._2) []
    , funD 'morphMap (tiConstructors info <&> mkMorphCon)
    , funD 'morphLiftConstraint liftConstraintClauses
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
            , (n, gadtC [n] [] (pure (appSubsts morphWithNessOf x)))
            )
        embedWits =
            tcEmbeds contents ^.. Lens.folded <&>
            \x ->
            let n = witPrefix <> mkNiceTypeName x & mkName in
            ( x
            , ( n
                , gadtC [n] []
                    [t|$(pure (ConT ''MorphWitness `appSubsts` x `AppT` varA `AppT` varB)) ->
                        $(pure morphWithNessOf) $(pure varA) $(pure varB)|])
            )
        witnesses = nodeWits <> embedWits & Map.fromList
        varA = VarT (mkName "a")
        varB = VarT (mkName "b")
        witPrefix = "M_" <> niceName (tiName info) <> "_"
        morphWithNessOf = ConT ''MorphWitness `AppT` src `AppT` dst
        liftConstraintClauses
            | Map.null witnesses = [clause [] (normalB (lamCaseE [])) []]
            | otherwise =
                (nodeWits ^.. traverse . Lens._2 . Lens._1 <&> liftNodeConstraint) <>
                (embedWits ^.. traverse . Lens._2 . Lens._1 <&> liftEmbedConstraint)
        liftNodeConstraint n = clause [conP n [], wildP] (normalB [|id|]) []
        liftEmbedConstraint n =
            clause [conP n [varP varW], varP varProxy]
            (normalB [|morphLiftConstraint $(varE varW) $(varE varProxy)|]) []
        varW = mkName "w"
        varProxy = mkName "p"
        mkMorphCon con =
            clause [varP varF, p] b []
            where
                (p, b) = morphCon 0 witnesses con

varF :: Name
varF = mkName "_f"

morphCon :: Int -> Map Type (Name, a) -> (Name, b, [Either c CtrTypePattern]) -> (Q Pat, Q Body)
morphCon i witnesses (n, _, fields) =
    ( conP n (cVars <&> varP)
    , normalB (foldl appE (conE n) (zipWith bodyFor fields cVars))
    )
    where
        cVars =
            [i ..] <&> show <&> ('x':) <&> mkName
            & take (length fields)
        f = varE varF
        bodyFor Left{} v = varE v
        bodyFor (Right x) v = [|$(bodyForPat x) $(varE v)|]
        bodyForPat (Node x) = [|$f $(conE (witnesses ^?! Lens.ix x . Lens._1))|]
        bodyForPat (InContainer _ pat) = [|fmap $(bodyForPat pat)|]
        bodyForPat (FlatEmbed x) =
            lamCaseE
            (tiConstructors x
                <&> morphCon (i + length cVars) witnesses
                <&> \(p, b) -> match p b []
            )
        bodyForPat (GenEmbed t) = [|morphMap ($f . $(conE (witnesses ^?! Lens.ix t . Lens._1)))|]

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
