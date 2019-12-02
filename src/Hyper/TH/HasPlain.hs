{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'HasHPlain' instances via @TemplateHaskell@

module Hyper.TH.HasPlain
    ( makeHasHPlain
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import qualified Data.Map as Map
import           Hyper.Class.HasPlain
import           Hyper.TH.Internal.Utils
import           Hyper.Type (GetHyperType)
import           Hyper.Type.Pure (Pure(..), _Pure)
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

-- | Generate a 'HasHPlain' instance
makeHasHPlain :: [Name] -> DecsQ
makeHasHPlain x = traverse makeOne x <&> concat

makeOne :: Name -> Q [Dec]
makeOne typeName = makeTypeInfo typeName >>= makeHasHPlainForType

makeHasHPlainForType :: TypeInfo -> Q [Dec]
makeHasHPlainForType info =
    do
        ctrs <- traverse (makeCtr (tiHyperParam info)) (tiConstructors info)
        let typs = ctrs >>= (^. Lens._4) & filter (not . anHPlainOfCons)
        let plains =
                typs
                >>=
                \case
                ConT hplain `AppT` x | hplain == ''HPlain -> [x]
                _ -> []
        plainsCtx <- plains <&> AppT (ConT ''HasHPlain) & simplifyContext
        showCtx <- typs <&> AppT (ConT ''Show) & simplifyContext
        let makeDeriv cls =
                typs <&> AppT (ConT cls) & simplifyContext
                <&>
                \ctx -> StandaloneDerivD Nothing ctx (ConT cls `AppT` (ConT ''HPlain `AppT` tiInstance info))
        (:) <$> instanceD
                (pure (showCtx <> plainsCtx))
                (pure (ConT ''HasHPlain `AppT` tiInstance info))
                [ dataInstD (pure []) ''HPlain [pure (tiInstance info)] Nothing (ctrs <&> pure . (^. Lens._1)) []
                , funD 'hPlain
                    [ clause []
                        ( normalB
                            ((VarE 'Lens.iso `AppE` VarE fromPlain `AppE` VarE toPlain)
                                `dot`
                                (VarE 'Lens.from `AppE` VarE '_Pure)
                                & pure
                            )
                        )
                        [ funD toPlain (ctrs <&> pure . (^. Lens._2))
                        , funD fromPlain (ctrs <&> pure . (^. Lens._3))
                        ]
                    ]
                ]
            <*> traverse makeDeriv [''Eq, ''Ord, ''Show]
    where
        anHPlainOfCons (ConT hplain `AppT` x)
            | hplain == ''HPlain =
                case unapply x of
                (ConT{}, _) -> True
                _ -> False
        anHPlainOfCons _ = False
        toPlain = mkName "toPlain"
        fromPlain = mkName "fromPlain"

data FieldInfo = FieldInfo
    { fieldPlainType :: Type
    , fieldToPlain :: Exp -> Exp
    , fieldFromPlain :: Exp -> Exp
    }

data FlatInfo = FlatInfo
    { flatIsEmbed :: Bool
    , flatCtr :: Name
    , flatFields :: [Field]
    }

data Field
    = NodeField FieldInfo
    | FlatFields FlatInfo

makeCtr ::
    Name ->
    (Name, D.ConstructorVariant, [Either Type CtrTypePattern]) ->
    Q (Con, Clause, Clause, [Type])
makeCtr param (cName, _, cFields) =
    traverse (forField True) cFields
    <&>
    \xs ->
    let plainTypes = xs >>= plainFieldTypes
        cVars = [0::Int ..] <&> show <&> ('x':) <&> mkName & take (length plainTypes)
    in
    ( plainTypes
        <&> (Bang NoSourceUnpackedness NoSourceStrictness, )
        & NormalC pcon
    , zipWith ($) (xs >>= toPlainFields) (cVars <&> VarE)
        & foldl AppE (ConE pcon)
        & NormalB
        & \x ->
            Clause [ConP cName (toPlainPat cVars xs ^. Lens._1)] x []
    , fromPlainFields cVars xs ^. Lens._1
        & foldl AppE (ConE cName)
        & NormalB
        & \x -> Clause [ConP pcon (cVars <&> VarP)] x []
    , xs >>= fieldContext
    )
    where
        plainFieldTypes (NodeField x) = [fieldPlainType x]
        plainFieldTypes (FlatFields x) = flatFields x >>= plainFieldTypes
        toPlainFields (NodeField x) = [fieldToPlain x]
        toPlainFields (FlatFields x) = flatFields x >>= toPlainFields
        toPlainPat cs [] = ([], cs)
        toPlainPat (c:cs) (NodeField{} : xs) = toPlainPat cs xs & Lens._1 %~ (VarP c :)
        toPlainPat cs0 (FlatFields x : xs) =
            toPlainPat cs1 xs & Lens._1 %~ (res :)
            where
                res | flatIsEmbed x = embed
                    | otherwise = ConP 'Pure [embed]
                embed = ConP (flatCtr x) r
                (r, cs1) = toPlainPat cs0 (flatFields x)
        toPlainPat [] _ = error "out of variables"
        fromPlainFields cs [] = ([], cs)
        fromPlainFields (c:cs) (NodeField x : xs) =
            fromPlainFields cs xs & Lens._1 %~ (fieldFromPlain x (VarE c) :)
        fromPlainFields cs0 (FlatFields x : xs) =
            fromPlainFields cs1 xs & Lens._1 %~ (res :)
            where
                res | flatIsEmbed x = embed
                    | otherwise = ConE 'Pure `AppE` embed
                embed = foldl AppE (ConE (flatCtr x)) r
                (r, cs1) = fromPlainFields cs0 (flatFields x)
        fromPlainFields [] _ = error "out of variables"
        pcon =
            show cName & reverse & takeWhile (/= '.') & reverse
            & (<> "P") & mkName
        forField _ (Left t) =
            NodeField FieldInfo
            { fieldPlainType = normalizeType t
            , fieldToPlain = id
            , fieldFromPlain = id
            } & pure
        forField isTop (Right x) = forPat isTop x
        forPat isTop (Node x) = forGen isTop x
        forPat isTop (GenEmbed x) = forGen isTop x
        forPat _ (InContainer t p) =
            NodeField FieldInfo
            { fieldPlainType = t `AppT` patType p
            , fieldToPlain = AppE (VarE 'fmap `AppE` InfixE (Just (VarE 'hPlain)) (VarE '(#)) Nothing)
            , fieldFromPlain = AppE (VarE 'fmap `AppE` InfixE Nothing (VarE '(^.)) (Just (VarE 'hPlain)))
            } & pure
            where
                patType (Node x) = ConT ''HPlain `AppT` x
                patType (GenEmbed x) = ConT ''HPlain `AppT` x
                patType (FlatEmbed x) = ConT ''HPlain `AppT` tiInstance x
                patType (InContainer t' p') = t' `AppT` patType p'
        forPat isTop (FlatEmbed x) =
            case tiConstructors x of
            [(n, _, xs)] -> traverse (forField False) xs <&> FlatInfo isTop n <&> FlatFields
            _ -> forGen isTop (tiInstance x)
        forGen isTop t =
            case unapply t of
            (ConT c, args) ->
                reify c
                >>=
                \case
                FamilyI{} -> gen -- Not expanding type families currently
                _ ->
                    do
                        inner <- D.reifyDatatype c
                        let subst =
                                args <> [VarT param]
                                & zip (D.datatypeVars inner <&> D.tvName)
                                & Map.fromList
                        case D.datatypeCons inner of
                            [x] ->
                                D.constructorFields x
                                <&> D.applySubstitution subst
                                & traverse (matchType param)
                                >>= traverse (forField False)
                                <&> FlatInfo isTop (D.constructorName x)
                                <&> FlatFields
                            _ -> gen
            _ -> gen
            where
                gen =
                    NodeField FieldInfo
                    { fieldPlainType = ConT ''HPlain `AppT` t
                    , fieldToPlain = InfixE (Just (VarE 'hPlain)) (VarE '(#)) . Just
                    , fieldFromPlain = \f -> InfixE (Just f) (VarE '(^.)) (Just (VarE 'hPlain))
                    } & pure
        normalizeType (ConT g `AppT` VarT v)
            | g == ''GetHyperType && v == param = ConT ''Pure
        normalizeType (x `AppT` y) = normalizeType x `AppT` normalizeType y
        normalizeType x = x
        fieldContext (NodeField x) = [fieldPlainType x]
        fieldContext (FlatFields x) = flatFields x >>= fieldContext
